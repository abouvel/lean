FROM node:22-bookworm-slim
ARG CODEX_VERSION=0.162.0
RUN apt-get update && apt-get install -y --no-install-recommends \
    bash ca-certificates curl git python3 ripgrep libgmp10 libstdc++6 \
    && rm -rf /var/lib/apt/lists/* \
    && npm install -g @openai/codex@${CODEX_VERSION} \
    && groupadd -g 1100 researcher && useradd -m -u 1100 -g 1100 researcher
ENV PATH="/opt/lean/bin:${PATH}" HOME=/home/researcher
ENV CODEX_HOME=/home/researcher/.codex
WORKDIR /workspace
USER 1100:1100
CMD ["bash"]
