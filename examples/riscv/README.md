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

## Building HolBA

See the [general README](https://github.com/kth-step/HolBA/blob/master/README.md) for information on how to build HolBA.
