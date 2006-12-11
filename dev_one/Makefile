#are we called from the kernel makefile?
ifneq ($(KERNELRELEASE),)
	 obj-m := dev_one.o
else
	#if not, run the kernel makefile
	KERNELDIR ?= /lib/modules/$(shell uname -r)/build
	PWD := $(shell pwd)

default:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

endif

clean:
	rm -rf *.o *~ core .depend .*.cmd *.mod.c .tmp_versions Module.symvers
