#!/bin/bash

# check if the ports are available
declare -a ports_to_check=(
    ${EMBEXP_UART_PORT}
    ${EMBEXP_GDBS_PORT}
)

# loop over the ports
for port in "${ports_to_check[@]}"
do
    echo "checking port ${port}"
    # fail if one of them is not open locally
    if lsof -Pi :${port} -sTCP:LISTEN -t > /dev/null ; then
        exit 1
    fi
done

echo "PORTS ARE CLOSED"

exit 0

