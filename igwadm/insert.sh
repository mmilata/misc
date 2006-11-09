#!/bin/bash

for x in `seq 1 254`; do
	mysql igwadm -e "INSERT INTO users (ap_id,grp_id,name) VALUES (1,2,'Klient-1-$x'); INSERT INTO addr (user_id,ip,allowed) VALUES (LAST_INSERT_ID(),'192.168.1.$x',1);"
done
