#!/bin/bash

echo -1000 > /proc/$$/oom_score_adj
BASE_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

while true; do
    $BASE_DIR/translator.py "$@"
    exit_status=$?

    if [ $exit_status -eq 0 ]; then
        break
    fi

    echo "The translator crahses with code $exit_status. Now rebooting it..."
    sleep 1
done

echo "All succeed!"
