# --- Build stage (with cache) ---
# Enable BuildKit cache mounts on Fly automatically
FROM haskell:9.4 AS build
WORKDIR /app

# Project metadata first for better cache keying
COPY stack.yaml ./
COPY *.cabal   ./

# Cache Stack’s dirs so GHC + packages persist across builds
# (Fly's builder supports BuildKit; these mounts significantly speed up rebuilds)
RUN --mount=type=cache,target=/root/.stack stack setup --install-ghc --no-terminal

# Source + static
COPY src ./src
COPY app ./app
COPY static ./static
COPY prompts ./prompts

RUN --mount=type=cache,target=/root/.stack \
    --mount=type=cache,target=/app/.stack-work \
    stack build --copy-bins --local-bin-path /app/bin --install-ghc --no-terminal :web

# --- Runtime stage ---
FROM debian:bullseye-slim
RUN apt-get update -y && \
    apt-get install -y --no-install-recommends libgmp10 libtinfo6 ca-certificates && \
    rm -rf /var/lib/apt/lists/*

RUN useradd -m app
WORKDIR /app

# This image sets no locale, so GHC's readFile and putStrLn fall back to ASCII
# -- and prompts/transcribe.txt is UTF-8 with the logical symbols in it. That
# broke every transcription on the host while development on macOS, which
# supplies UTF-8, worked perfectly. Web.hs forces the encoding at startup as
# well, so this is the second of two layers rather than the only one.
ENV LANG=C.UTF-8 LC_ALL=C.UTF-8

# Copy the web binary and static assets
COPY --from=build /app/bin/web /usr/local/bin/web
COPY static ./static
# The /transcribe route reads its prompt from here at request time.
COPY prompts ./prompts

EXPOSE 8080
ENV PORT=8080

USER app
CMD ["web"]

