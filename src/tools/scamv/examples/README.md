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
Run experiment generation and experiments themselves. Now we are operating in the directory `${HOLBA_DIR}/src/tools/scamv/examples`.

The configuration and notes are in text files in `expgenruns`. The first line is the scamv command line and the following lines are unstructured notes.

Execute the following commands in order and in different shells and let them run in parallel to each other.
1. `./scripts/1-gen.sh cav_2019-12-03 qc_previct5`
1. `./scripts/2-connect.sh rpi3`
1. `./scripts/3-run.sh arm8/exps2`

See status of the run with `./scripts/4-status.sh`.

Update HolBA and EmbExp-Box with `./scripts/5-update.sh `.


## Finish
After completing an experiment generation or run, don't forget to commit and push in `${HOLBA_DIR}/logs/EmbExp-Logs`.

