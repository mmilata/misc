#!/bin/sh
#
# pokud je ntb pripojen k ac a k ethernetu, zapne wol,
# jinak jej vypne
# volano pred suspendem z duvodu setreni energie (zapnuty wol zere ~200mW)

IFACE="eth0"

if ( grep "on-line" /proc/acpi/ac_adapter/AC/state 2>&1 >/dev/null \
&& mii-tool $IFACE 2>&1 | grep "link ok" >/dev/null ); then
	echo "Enabling WOL" 
	ethtool -s $IFACE wol g
else
	echo "Disabling WOL"
	ethtool -s $IFACE wol d
fi
