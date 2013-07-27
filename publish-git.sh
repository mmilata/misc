#!/bin/bash -x

DESTHOST="b42.cz"
DESTDIR="git"

if [ $# -ne 2 ]; then
	echo "Usage: $0 <repo> <description>"
	exit 1
fi

REPO=$1
DESC=$2
BARE=$REPO.git

set -e

echo "Creating bare clone ..."
git clone --bare $REPO $BARE
git config -f $BARE/config --remove-section remote.origin
mv $BARE/hooks/post-update{.sample,}
echo $DESC > $BARE/description

echo "Copying $BARE to $DESTHOST ..."
scp -r $BARE $DESTHOST:$DESTDIR/
rm -rf $BARE

echo "Running post-update"
ssh $DESTHOST -- "cd $DESTDIR/$BARE/hooks && ./post-update"

echo "Backing up original repository"
mv $REPO $REPO.orig

echo "Checking out remote repository"
git clone $DESTHOST:$DESTDIR/$BARE $REPO

echo "Done -- you can now delete $REPO.orig"
