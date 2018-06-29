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

SOURCEFILE=$1

FUNC=$2

FRAMACARGS='-wp -wp-rte -cpp-command'

CPPCOMMAND='gcc -C -E -I/home/simon/Systerel/S2OPC/csrc/services/bgenc -I/home/simon/Systerel/S2OPC/csrc/services -I/home/simon/Systerel/S2OPC/install/include/'

WPFUNC='-wp-fct'

FILESWCONTRACTS="service_write_decode_bs.c response_write_bs.c service_browse_decode_bs.c constants_bs.c msg_read_request_bs.c address_space_bs.c msg_read_request_bs.c"

if [[ -z $SOURCEFILE || $SOURCEFILE == 'all' ]]
then
    echo "WP verification for all annotated files."
    frama-c $FRAMACARGS "$CPPCOMMAND" $FILESWCONTRACTS
else
    if [[ -r $SOURCEFILE && -z $FUNC ]]
    then
        echo "Verification du fichier $SOURCEFILE"
        frama-c $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE
    else
        if [[ -r $SOURCEFILE && 'gui' != $FUNC ]]
        then
            echo "Verification de la fonction $FUNC dans $SOURCEFILE"
            frama-c $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE $WPFUNC $FUNC
        else
            if [[ -r $SOURCEFILE && 'gui' == $FUNC ]]
            then
                frama-c-gui $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE
            fi
        fi
    fi
fi
