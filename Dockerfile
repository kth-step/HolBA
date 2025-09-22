FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

ENV HOLBA_POLYML_VERSION=PREPACKAGED
ENV HOLBA_Z3_VERSION=4.13.4
ENV HOLBA_HOL4_VERSION=trindemossen-1
ENV HOLBA_Z3_ASSET_SUFFIX=-x64-glibc-2.35.zip

# Create a non-root user with a known password
RUN useradd -m -s /bin/bash evaluser \
    && echo "evaluser:evalpass" | chpasswd \
    && usermod -aG sudo evaluser \
    && echo "evaluser ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

# Copy current directory into the user's home
COPY . /home/evaluser/

# Ensure the user owns their files
RUN chown -R evaluser:evaluser /home/evaluser

# Switch to the non-root user
USER evaluser
WORKDIR /home/evaluser

RUN ./scripts/setup/install_base.sh

RUN ./scripts/setup/install_z3.sh

CMD ["bash"]
