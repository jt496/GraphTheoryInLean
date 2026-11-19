# The container that GitHub Codespaces (or VS Code's Dev Containers) opens this
# repository in: elan, which installs the toolchain named in lean-toolchain the
# first time `lake` runs.
FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

USER vscode
WORKDIR /home/vscode

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"
