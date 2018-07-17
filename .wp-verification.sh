#!/bin/bash

# Licensed to Systerel under one or more contributor license
# agreements. See the NOTICE file distributed with this work
# for additional information regarding copyright ownership.
# Systerel licenses this file to you under the Apache
# License, Version 2.0 (the "License"); you may not use this
# file except in compliance with the License. You may obtain
# a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.

# Script to check wp verification

ENV="/home/simon/Systerel/S2OPC"

if [[ -n $1 && $1 == "-gui" ]]
then
    FRAMAC="frama-c-gui"
    SOURCEFILE=$2
    FUNC=$3
else
    FRAMAC="frama-c"
    SOURCEFILE=$1
    FUNC=$2
fi

FRAMACARGS='-wp -wp-rte -cpp-command'

CPPCOMMAND="gcc -C -E -I$ENV/csrc/services/b2c -I$ENV/csrc/services/bgenc -I$ENV/csrc/services -I$ENV/install/include -I$ENV/tests/wp"

WPFUNC='-wp-fct'

FILESWCONTRACTS="service_write_decode_bs.c response_write_bs.c service_browse_decode_bs.c constants_bs.c msg_read_request_bs.c address_space_bs.c msg_read_request_bs.c"

if [[ -z $SOURCEFILE || $SOURCEFILE == 'all' ]]
then
    echo "WP verification for all annotated files."
    $FRAMAC $FRAMACARGS "$CPPCOMMAND" $FILESWCONTRACTS
else
    if [[ -r $SOURCEFILE && -z $FUNC ]]
    then
        echo "WP verification on file $SOURCEFILE"
        $FRAMAC $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE
    else
        $FRAMAC $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE $WPFUNC $FUNC
    fi
fi
