#!/bin/bash

# Copyright (C) 2018 Systerel and others.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.


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
