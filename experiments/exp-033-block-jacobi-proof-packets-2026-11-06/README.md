# Block Jacobi proof packets

The original archive and both entries are preserved in [original](original/).
The batch formalizes each of the ten active statements separately, once per memory condition.
These are source-assisted formalizations. Each job starts from a clean Lean workspace.
Results from other jobs are not imported as prerequisites.

| Task | TeX label | Source lines |
| --- | --- | --- |
| binary-tree-reduction | `theorem:parallel_binary_tree_reduction` | 180–216 |
| block-dot-product | `theorem:block_dot_product` | 235–291 |
| sequential-block-dot | `corollary:block_dot_product_sequential` | 312–343 |
| block-matrix-vector | `theorem:block_matrix_vector_product` | 353–393 |
| triangular-update | `lemma:traingular_update` | 403–452 |
| triangular-solve | `theorem:solution_of_a_traingular_system` | 457–490 |
| cholesky-factorization | `theorem:cholesky_factorization` | 500–545 |
| cholesky-solve | `theorem:cholesky_solve` | 550–610 |
| real-block-jacobi | `theorem:block_jacobi_real` | 613–693 |
| mixed-precision-block-jacobi | `theorem:mixed_precision_update_form_block_jacobi_in_floating_point_arithmetic` | 703–1270 |
