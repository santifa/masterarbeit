#!/bin/bash

# Copyright 2011 Cornell University
#
#
# This file is part of EventML - a tool aiming at specifying
# distributed protocols in an ML like language.  It is an interface
# to the logic of events and is compiled into Nuprl.  It is written
# by the NUPRL group of Cornell University, Ithaca, NY.
#
# EventML is a free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# EventML is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with EventML.  If not, see <http://www.gnu.org/licenses/>.
#
#  o Authors:     Vincent Rahli
#  o Affiliation: Cornell University, NUPRL group
#  o Date:        20 May 2011
#  o File name:   package.sh
#  o Description: Packaging script
#


VERSION=0.3
TMP_NUPRL=/tmp/nuprl

echo "Packaging starting."
echo

# Clone repo to a tmp directory
echo " ------ Cloning the repo..."
git clone -q ../. ${TMP_NUPRL}
echo

# Remove the papers dir from the copied repo
echo " ------ Removing the unecessary files from the cloned repo..."
rm -rf ${TMP_NUPRL}/esharp/papers
rm -rf ${TMP_NUPRL}/esharp/evaluators/erlang
echo

# Rename the esharp dir so that it contains the version number
# and so that it is called eventml
echo " ------ Adding the version number to the directory to package..."
mv ${TMP_NUPRL}/esharp ${TMP_NUPRL}/eventml-${VERSION}
echo

# Generate configure from configure.ac
echo " ------ Running autoconf..."
(cd ${TMP_NUPRL}/eventml-${VERSION}; autoconf)
echo

# Archive the eventml dir
echo " ------ Archiving directory..."
(cd ${TMP_NUPRL}; tar -czf eventml_${VERSION}-src.tar.gz eventml-${VERSION})
echo

# Move the archive to the repo
echo " ------ Moving the archive into the repo..."
mv ${TMP_NUPRL}/eventml_${VERSION}-src.tar.gz ..
echo

# Remove the tmp copied repo
echo " ------ Removing the copied repo..."
rm -rf ${TMP_NUPRL}
echo

echo "Packaging done."
