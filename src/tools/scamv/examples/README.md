# Experimenting procedure

## Setup

Clone HolBA somewhere, change to the branch dev_scamv, setup and compile everything. This step can be repeated multiple times for different IDX (0-99).
```
HOLBA_PARENT_DIR=/path/to/this
IDX=1

HOLBA_DIR=${HOLBA_PARENT_DIR}/HolBA_scamv_${IDX}
HOLBA_OPT_DIR=${HOLBA_PARENT_DIR}/HolBA_opt

git clone https://github.com/kth-step/HolBA.git "${HOLBA_DIR}"
cd "${HOLBA_DIR}"
git checkout dev_scamv

cd src/tools/scamv/examples
./scripts/0-setup.sh "${IDX}" "${HOLBA_OPT_DIR}"
```

Setup the box connection configuration file `${HOLBA_OPT_DIR}/embexp/EmbExp-Box/config/networks.json`.


## Running
Run experiment generation and experiments themselves. The configuration and notes are in text files in `${HOLBA_DIR}/src/tools/scamv/examples/expgenruns`. The first line is the scamv command line and the following lines are unstructured notes. The following script blocks have to be executed in different shells.
```
cd "${HOLBA_DIR}/src/tools/scamv/examples"
./scripts/1-connect.sh rpi3
```
```
cd "${HOLBA_DIR}/src/tools/scamv/examples"
./scripts/2-gen.sh cav_2019-12-03 qc_previct5
```
```
cd "${HOLBA_DIR}/src/tools/scamv/examples"
./scripts/3-run.sh arm8/exps2
```


## Finish
After completing an experiment generation or run, don't forget to commit and push in `${HOLBA_DIR}/logs/EmbExp-Logs`.

