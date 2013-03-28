#!/bin/bash

NEW_FILE="$1"
OLD_FILE="$2"

SHELF_NAME="compare-times-shelf"

trap "hg import --no-commit $SHELF_NAME" SIGINT SIGTERM

# make the old version
#hg shelve --all --name $SHELF_NAME
hg diff > $SHELF_NAME && hg revert -a
make clean
make timed 2>&1 | tee "$OLD_FILE"


# make the current version
hg import --no-commit $SHELF_NAME && mv $SHELF_NAME "$SHELF_NAME-$(date | base64).bak"
make clean
make timed 2>&1 | tee "$NEW_FILE"
