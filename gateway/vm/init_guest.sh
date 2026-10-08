#!/bin/sh
set -eu
/bin/busybox mkdir -p /run /tmp /state
/bin/busybox mount -t tmpfs tmpfs /run
/bin/busybox mount -t tmpfs tmpfs /tmp
/bin/busybox hostname "sc01-vm-$(/bin/busybox cat /etc/sc01-role)"
/bin/busybox ip link set lo up
/bin/busybox ip link set eth0 up
role=$(/bin/busybox cat /etc/sc01-role)
if [ "$role" = A ]; then
    /bin/busybox ip addr add 192.0.2.1/30 dev eth0
else
    /bin/busybox ip addr add 192.0.2.2/30 dev eth0
fi
/bin/busybox stty -echo -icanon min 1 time 0 < /dev/ttyAMA0
exec /usr/bin/python3 -u /opt/sc01/guest.py < /dev/ttyAMA0 > /dev/ttyAMA0 2> /dev/ttyAMA0
