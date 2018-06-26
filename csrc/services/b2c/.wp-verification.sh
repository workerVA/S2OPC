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

if [[ -n $SOURCEFILE ]]
then
    if [[ -z $FUNC ]]
    then
        echo "Verification du fichier $SOURCEFILE"
        frama-c $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE
    else
        echo "Verification de la fonction $FUNC dans $SOURCEFILE"
        frama-c $FRAMACARGS "$CPPCOMMAND" $SOURCEFILE $WPFUNC $FUNC
    fi
else
    echo "None"
fi

