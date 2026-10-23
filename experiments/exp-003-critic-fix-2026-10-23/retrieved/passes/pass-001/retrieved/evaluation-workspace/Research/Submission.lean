import Mathlib

/-! Algorithm 1 of Sahil Bhola, with zero-based list indexing. The second
half starts at ceil(length/2); missing partners are carried without rounding. -/
namespace Bhola

def depth (n : ℕ) : ℕ := Nat.clog 2 n

def offset (n : ℕ) : ℕ := (n + 1) / 2

/-- Pair the first block with the offset block. The carry branch is unchanged. -/
def pair (add : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => add x y :: pair add xs ys

def step (add : α → α → α) (xs : List α) : List α :=
  pair add (xs.take (offset xs.length)) (xs.drop (offset xs.length))

/-- Roundoff may depend deterministically on the level and output position. -/
def pairAt (add : ℕ → α → α → α) : ℕ → List α → List α → List α
  | _, [], ys => ys
  | _, xs, [] => xs
  | k, x :: xs, y :: ys => add k x y :: pairAt add (k+1) xs ys

def roundAt (add : ℕ → α → α → α) (xs : List α) : List α :=
  pairAt add 0 (xs.take (offset xs.length)) (xs.drop (offset xs.length))

def rounds (add : ℕ → ℕ → α → α → α) : ℕ → ℕ → List α → List α
  | 0, _, xs => xs
  | t+1, l, xs => rounds add t (l+1) (roundAt (add l) xs)

def algorithm (add : ℕ → ℕ → ℝ → ℝ → ℝ) (xs : List ℝ) : List ℝ :=
  rounds add (depth xs.length) 0 xs

/-- The paper's standard model; carries do not call this operation. -/
def roundedAdd (δ : ℕ → ℕ → ℝ) (l k : ℕ) (a b : ℝ) : ℝ :=
  (a + b) * (1 + δ l k)

noncomputable def gamma (d : ℕ) (u : ℝ) : ℝ := (d : ℝ) * u / (1 - (d : ℝ) * u)

theorem pairAt_length (f : ℕ → α → α → α) (k : ℕ) (xs ys : List α) :
    (pairAt f k xs ys).length = max xs.length ys.length := by
  induction xs generalizing k ys with
  | nil => simp [pairAt]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pairAt]
    | cons y ys => simp [pairAt, ih, Nat.succ_max_succ]

theorem roundAt_length (f : ℕ → α → α → α) (xs : List α) :
    (roundAt f xs).length = offset xs.length := by
  rw [roundAt, pairAt_length]
  simp only [List.length_take, List.length_drop, offset]
  omega

theorem pairAt_sum (k : ℕ) (xs ys : List ℝ) :
    (pairAt (fun _ a b => a + b) k xs ys).sum = xs.sum + ys.sum := by
  induction xs generalizing k ys with
  | nil => simp [pairAt]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pairAt]
    | cons y ys => simp only [pairAt, List.sum_cons, ih]; ring

theorem roundAt_sum (xs : List ℝ) :
    (roundAt (fun _ a b => a + b) xs).sum = xs.sum := by
  rw [roundAt, pairAt_sum, ← List.sum_append, List.take_append_drop]

theorem rounds_sum (t l : ℕ) (xs : List ℝ) :
    (rounds (fun _ _ a b => a + b) t l xs).sum = xs.sum := by
  induction t generalizing l xs with
  | zero => rfl
  | succ t ih => rw [rounds, ih, roundAt_sum]

theorem algorithm_exact (xs : List ℝ) :
    (algorithm (fun _ _ a b => a + b) xs).sum = xs.sum :=
  rounds_sum _ _ _

/-- An exact arithmetical characterization of the stated logarithmic depth. -/
theorem depth_le_iff (n t : ℕ) : depth n ≤ t ↔ n ≤ 2 ^ t :=
  Nat.clog_le_iff_le_pow (by decide)

/-- Every active round halves the active length, rounding upwards. -/
theorem rounds_singleton_length (f : ℕ → ℕ → α → α → α)
    (t l : ℕ) (xs : List α) (hn : 0 < xs.length) (hb : xs.length ≤ 2^t) :
    (rounds f t l xs).length = 1 := by
  induction t generalizing l xs with
  | zero => simp only [pow_zero] at hb; simp [rounds]; omega
  | succ t ih =>
    rw [rounds]
    apply ih
    · rw [roundAt_length]; unfold offset; omega
    · rw [roundAt_length]; unfold offset
      rw [pow_succ] at hb
      omega

theorem algorithm_singleton (xs : List ℝ) (hn : xs ≠ [])
    (f : ℕ → ℕ → ℝ → ℝ → ℝ) : (algorithm f xs).length = 1 := by
  apply rounds_singleton_length
  · exact List.length_pos_iff.mpr hn
  · exact (depth_le_iff _ _).mp le_rfl

/-- A path with at most d additions has the following elementary error bound. -/
theorem path_error (u : ℝ) (hu : 0 ≤ u) (ds : List ℝ)
    (hds : ∀ δ ∈ ds, |δ| ≤ u) :
    |(ds.map (fun δ => 1 + δ)).prod - 1| ≤ (1 + u)^ds.length - 1 := by
  induction ds with
  | nil => simp
  | cons δ ds ih =>
    have hd := hds δ (by simp)
    have ht := ih (by intro d h; exact hds d (by simp [h]))
    have hp : 0 ≤ (1+u)^ds.length - 1 := by
      have := one_le_pow₀ (n := ds.length) (by linarith : (1:ℝ) ≤ 1+u)
      linarith
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc
      |(1+δ) * (ds.map (fun δ => 1+δ)).prod - 1| =
          |((ds.map (fun δ => 1+δ)).prod - 1) * (1+δ) + δ| := by congr 1; ring
      _ ≤ |(ds.map (fun δ => 1+δ)).prod - 1| * |1+δ| + |δ| := by
        simpa [abs_mul] using abs_add_le
          (((ds.map (fun δ => 1+δ)).prod - 1) * (1+δ)) δ
      _ ≤ ((1+u)^ds.length-1) * (1+u) + u := by
        have hδ : |1+δ| ≤ 1+u := by
          calc |1+δ| ≤ |(1:ℝ)| + |δ| := abs_add_le _ _
               _ ≤ 1+u := by simpa using add_le_add_left hd 1
        exact add_le_add (mul_le_mul ht hδ (abs_nonneg _) hp) hd
      _ = (1+u)^ds.length * (1+u) - 1 := by ring

/-- The standard gamma bound, proved without assuming a product-error lemma. -/
theorem power_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ) (hn : (n:ℝ)*u < 1) :
    (1+u)^n - 1 ≤ gamma n u := by
  have core : ∀ n : ℕ, (n:ℝ)*u < 1 → (1+u)^n * (1-(n:ℝ)*u) ≤ 1 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : (k:ℝ)*u < 1 := by push_cast at hk; nlinarith
      have hi := ih hk'
      have hp : 0 ≤ (1+u)^k := pow_nonneg (by linarith) _
      have hq : 0 ≤ (k+1:ℝ)*u^2 := mul_nonneg (by positivity) (sq_nonneg _)
      calc
        (1+u)^(k+1) * (1-(↑(k+1):ℝ)*u) =
            (1+u)^k * (1-(k:ℝ)*u) - (1+u)^k * ((k+1)*u^2) := by
              rw [pow_succ]; push_cast; ring
        _ ≤ (1+u)^k * (1-(k:ℝ)*u) := sub_le_self _ (mul_nonneg hp hq)
        _ ≤ 1 := hi
  unfold gamma
  apply (le_div_iff₀ (by linarith : 0 < 1-(n:ℝ)*u)).mpr
  have := core n hn
  nlinarith

theorem path_gamma (u : ℝ) (hu : 0 ≤ u) (ds : List ℝ)
    (hds : ∀ δ ∈ ds, |δ| ≤ u) (hn : (ds.length:ℝ)*u < 1) :
    |(ds.map (fun δ => 1+δ)).prod - 1| ≤ gamma ds.length u :=
  (path_error u hu ds hds).trans (power_gamma u hu ds.length hn)

end Bhola
