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

if [[ -z $ENV ]]
then
    echo "Environnement variable ENV not set, assuming at root of project."
    ENV=$(pwd)
fi

HEADERDIR=$(find $ENV -type f -name '*.h' | sed -r 's|/[^/]+$||' | sort -u | sed -r "s|^|-I|" | tr '\n' ' ')

CPPCOMMAND="gcc -C -E $HEADERDIR"

if [[ -n $1 && $1 == "-gui" ]]
then
    FRAMAC="frama-c-gui"
    shift
else
    FRAMAC="frama-c"
fi
SOURCEFILE=$1
FUNC=$2

WPARGS='-wp -wp-rte -wp-timeout=30 -cpp-command'

WPFUNC='-wp-fct'

FILESWITHCONTRACTSBCK="service_write_decode_bs.c response_write_bs.c service_browse_decode_bs.c constants_bs.c msg_read_request_bs.c address_space_bs.c"
FILESWITHCONTRACTS=$(grep -I -r -ls -e "/\*@" -e "//@" csrc/ | sort | sed '/^.*\.h/d')

if [[ -n $SOURCEFILE ]]
then
    if [[ -r $SOURCEFILE ]]
    then
        FILESTOPROVE=$SOURCEFILE
        echo "WP verification of $SOURCEFILE."
    else
        echo "No files to prove."
        exit 0
    fi
else
    for i in $FILESWITHCONTRACTS
    do
        FILESTOPROVE=$FILESTOPROVE" "$ENV/$i
    done
    echo "WP verification for all annotated files."
fi
FRAMACLOG="wp_log"
EXITCODE=0

rm -f "wp-verification.tap"
mkdir -p $FRAMACLOG

NUM=0
for f in $FILESTOPROVE
do
    let NUM=$NUM+1
    NAME=$(basename $f)
    START=$SECONDS
    $FRAMAC $WPARGS "$CPPCOMMAND" $f -then -report > "$FRAMACLOG/$NAME.log"
    END=$SECONDS
    if [[ -z $(grep "Status Report Summary" "$FRAMACLOG/$NAME.log") ]]
    then
        echo -e "\033[0;31mError   \033[0;0m:" $f
        echo not ok $NUM - $f : Error on file >> "wp-verification.tap"
        EXITCODE=2
    else
        NBTOTAL=$(grep "Total" "$FRAMACLOG/$NAME.log" | sed 's/[^0-9]*//g')
        NBVALID=$(grep "Completely validated" "$FRAMACLOG/$NAME.log" | sed 's/[^0-9]*//g')
        NBCONSIDERVALID=$(grep "Considered valid" "$FRAMACLOG/$NAME.log" | sed 's/[^0-9]*//g')
        if [[ -z $(grep "To be validated" "$FRAMACLOG/$NAME.log") ]]
        then
            echo -e "\033[0;32mProved  \033[0;0m: $f ($(($NBVALID+$NBCONSIDERVALID))/$NBTOTAL) $((END-START))"
            echo ok $NUM - $f : Passed >> "wp-verification.tap"
            rm "$FRAMACLOG/$NAME.log"
        else
            echo "Unproved: $f ($(($NBVALID+$NBCONSIDERVALID))/$NBTOTAL) $((END-START))"
            echo not ok $NUM - $f : Unproved contracts >> "wp-verification.tap"
            EXITCODE=1
        fi
    fi
done
if [[ $NUM -gt 0 ]]
then
    echo "1..$NUM" >> "wp-verification.tap"
fi

exit $EXITCODE
