#!/bin/bash
#

SCALE=3

line=`head -n 1 /proc/stat`
user1=`echo $line | cut -d ' ' -f 2`
nicep1=`echo $line | cut -d ' ' -f 3`
system1=`echo $line | cut -d ' ' -f 4`
idle1=`echo $line | cut -d ' ' -f 5`
if [ `uname -r | cut -b -3` = "2.6" ]; then
	iowait1=`echo $line | cut -d ' ' -f 6`
	irq1=`echo $line | cut -d ' ' -f 7`
	softirq1=`echo $line | cut -d ' ' -f 8`
	all1=$(( $user1+$nicep1+$system1+$idle1+iowait1+irq1+softirq1 ))
else
	all1=$(( $user1+$nicep1+$system1+$idle1 ))
fi

echo -e "\t\tUSER\tSYSTEM\tIDLE\tSoftIRQ"

while true; do
	sleep 2;
	line=`head -n 1 /proc/stat`
	user2=`echo $line | cut -d ' ' -f 2`
	nicep2=`echo $line | cut -d ' ' -f 3`
	system2=`echo $line | cut -d ' ' -f 4`
	idle2=`echo $line | cut -d ' ' -f 5`
	if [ `uname -r | cut -b -3` = "2.6" ]; then
		iowait2=`echo $line | cut -d ' ' -f 6`
		irq2=`echo $line | cut -d ' ' -f 7`
		softirq2=`echo $line | cut -d ' ' -f 8`
		all2=$(( $user2+$nicep2+$system2+$idle2+iowait2+irq2+softirq2 ))
	else
		all2=$(( $user2+$nicep2+$system2+$idle2 ))
	fi

	per_idle=`echo "scale=$SCALE; (($idle2-$idle1)/($all2-$all1))*100" | bc`
	per_sys=`echo "scale=$SCALE; (($system2-$system1)/($all2-$all1))*100" | bc`
	per_user=`echo "scale=$SCALE; (($user2-$user1)/($all2-$all1))*100" | bc`
	if [ `uname -r | cut -b -3` = "2.6" ]; then
		per_sirq=`echo "scale=$SCALE; (($softirq2-$softirq1)/($all2-$all1))*100" | bc`
	fi
	ts=`date "+%H:%M:%S"`

	echo -e "$ts\t$per_user%\t$per_sys%\t$per_idle%\t$per_sirq%"

	user1=$user2
	nicep1=$nicep2
	system1=$system2
	idle1=$idle2
	iowait1=$iowait2
	irq1=$irq2
	softirq1=$softirq2
	all1=$all2
done

