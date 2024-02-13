# Prerequisites for RISC-V examples 

## Intalling the RISC-V cross-compilation toolchain

Clone the RISC-V GNU Compiler Toolchain:

```shell
git clone https://github.com/riscv/riscv-gnu-toolchain
```

Install the prerequisites, e.g., on Ubuntu:

```shell
sudo apt-get install autoconf automake autotools-dev curl python3 python3-pip libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev ninja-build git cmake libglib2.0-dev
```

Configure and build Linux cross-compiler:

```shell
./configure --prefix=/path/to/riscv
make linux
```

## Installing and building HolBA

To bootstrap Poly/ML, HOL4, and HolBA (may take tens of minutes):

```shell
git clone https://github.com/kth-step/HolBA.git
cd HolBA
./scripts/setup/install_all.sh
./configure.sh
make main
```
