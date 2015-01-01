#!/bin/bash

set -x

ETHIP="192.168.43.1"
OUTDEV="wlp3s0"
DEV="$1"

if ! nmcli dev | egrep ^$DEV\\W | fgrep unmanaged; then
    echo "Device managed by NM or not found"
    exit 1
fi

ifconfig $DEV $ETHIP netmask 255.255.255.0
echo 1 > /proc/sys/net/ipv4/ip_forward
iptables -t nat -A POSTROUTING -o $OUTDEV -j MASQUERADE

dnsmasq --interface "$DEV" \
        --except-interface lo \
        --bind-interfaces \
        --keep-in-foreground \
        --dhcp-range 192.168.43.16,192.168.43.254

iptables -t nat -D POSTROUTING -o $OUTDEV -j MASQUERADE
