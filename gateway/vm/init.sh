#!/bin/sh
set -eu
/bin/busybox mount -t proc proc /proc
/bin/busybox mount -t sysfs sysfs /sys
/bin/busybox mount -t devtmpfs devtmpfs /dev
/bin/busybox mkdir -p /state
/sbin/modprobe virtio_mmio
/sbin/modprobe virtio_net
/sbin/modprobe virtio_blk
/sbin/modprobe ext4
/bin/busybox mount -t ext4 /dev/vda /state
for filesystem in proc sys dev; do
    /bin/busybox mount --move "/$filesystem" "/state/$filesystem"
done
# bubblewrap must pivot from a normal mounted root, not the initial rootfs.
exec /bin/busybox switch_root /state /sbin/sc01-init
