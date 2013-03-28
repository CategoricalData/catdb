#!/bin/bash

NEW_FILE="$1"
OLD_FILE="$2"

SHELF_NAME="compare-times-shelf"

trap "hg unshelve --name $SHELF_NAME" SIGINT SIGTERM

# make the old version
hg shelve --all --name $SHELF_NAME
make clean
make timed 2>&1 | tee "$OLD_FILE"


# make the current version
hg unshelve --all --name $SHELF_NAME
make clean
make timed 2>&1 | tee "$NEW_FILE"
