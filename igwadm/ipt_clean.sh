#!/bin/bash -x

IPT="iptables"

$IPT -F
$IPT -t nat -F
$IPT -t mangle -F

$IPT -X igwadm
$IPT -X igwadm_INPUT
$IPT -X igwadm_OUTPUT

$IPT -t nat -X igwadm_PREROUTING
$IPT -t nat -X igwadm_POSTROUTING

$IPT -t mangle -X igwadm_OUTPUT
$IPT -t mangle -X igwadm
$IPT -t mangle -X igwadm_PREROUTING
$IPT -t mangle -X igwadm_POSTROUTING
