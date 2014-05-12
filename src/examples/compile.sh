#!/bin/bash

AGDA_STD_LIB="$HOME/.lib/agda/lib-0.7/src/"

SRC=$1



agda --include-path="$AGDA_STD_LIB" --include-path="." --epic "$SRC"
