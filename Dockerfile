FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

ENV HOLBA_POLYML_VERSION=v5.9.1
ENV HOLBA_Z3_VERSION=4.13.4
ENV HOLBA_HOL4_VERSION=trindemossen-1
ENV HOLBA_Z3_ASSET_SUFFIX=-x64-glibc-2.35.zip

# Install required dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    unzip \
    tar \
    wget \
    build-essential \
    python3 \
    python3-pip \
    sudo \
    && rm -rf /var/lib/apt/lists/*

# Create a non-root user with a known password
RUN useradd -ms /bin/bash evaluser \
    && echo "evaluser:evalpass" | chpasswd \
    && usermod -aG sudo evaluser \
    && echo "evaluser ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

# Setup opt directory
ENV HOLBA_OPT_DIR=/home/evaluser/HolBA_opt
RUN mkdir -p $HOLBA_OPT_DIR && chown -R evaluser:evaluser $HOLBA_OPT_DIR

# Switch to the non-root user, copy into the container, run setup and configuration
# ---------------------------------------------------------------------------------
USER evaluser
WORKDIR /home/evaluser/HolBA

COPY --chown=evaluser:evaluser HolBA .

RUN ./scripts/setup/install_base.sh
RUN ./scripts/setup/install_z3.sh

RUN ./configure.sh

CMD ["bash", "-i", "-c", "source ./env.sh && exec bash -i"]
