# Dockerfile for Rocq-NN-Roll
# Using Coq 8.20.1 as base image

# Use Coq 8.20.1 image as base
FROM docker.io/coqorg/coq:8.20.1

# Install Coquelicot library
RUN opam install -y coq-coquelicot

# Create and set working directory with proper permissions
RUN mkdir -p /home/coq/rocq-nn-roll-prototype/target
WORKDIR /home/coq/rocq-nn-roll-prototype

# Copy the source code to the working directory
COPY . /home/coq/rocq-nn-roll-prototype

# Build the project using opam exec to ensure proper environment
RUN opam exec -- python3 ./build.py genprojf && opam exec -- python3 ./build.py compile

# Set default command (entrypoint will handle opam exec)
CMD ["bash", "--login"]