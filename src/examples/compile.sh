#!/bin/bash

AGDA_STD_LIB="$HOME/agda-stdlib/src/"

CMP=$1
SRC=$2



agda --include-path="$AGDA_STD_LIB" --include-path="." --$CMP "$SRC"
