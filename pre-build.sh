#!/bin/bash
# Script to generate data necessary to build the INGOPCS project:
#
# Steps:
# - generate sources files from B model
# - generate sources files for examples address space for tests

BMODEL_DIR=B_model
ADDSPACE_DIR=address_space_generation

echo "Pre-build log" > pre-build.log

echo "Generate C sources files from B model" | tee -a pre-build.log
make -C ./B_model >> pre-build.log
if [[ $? != 0 ]]; then
    echo "Error: generating C source files from B model" | tee -a pre-build.log
    exit 1
fi

echo "Generate address space C files for tests" | tee -a pre-build.log
make -C ./address_space_generation >> pre-build.log
if [[ $? != 0 ]]; then
    echo "Error: generating address spaces for tests" | tee -a pre-build.log
    exit 1
else
    echo "Terminated with SUCCESS" | tee -a pre-build.log
fi
