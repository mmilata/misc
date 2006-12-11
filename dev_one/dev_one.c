/*
 * mostly stolen from mem driver by <b42@centrum.cz>
 */

#include <linux/module.h>
#include <linux/init.h>

#include <linux/types.h>
#include <linux/fs.h>
#include <linux/kernel.h>
#include <linux/errno.h>
#include <linux/cdev.h>

#include <asm/uaccess.h>

MODULE_AUTHOR("b42");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("/dev/one driver");

static dev_t device;
static struct cdev cdev;
#define SEASIZE PAGE_SIZE
/* #define SEASIZE 1024 */
static char * sea_of_ones;

static ssize_t dev_one_write(struct file * filp, const char __user * buf,
		      size_t count, loff_t *fpos)
{
	return count;
}

static ssize_t dev_one_read(struct file * filp, char __user * buf,
			    size_t count, loff_t *fpos)
{
	size_t todo = count;

	while (todo) {
		size_t chunk = todo;

		if (chunk > SEASIZE)
			chunk = SEASIZE;
		if (copy_to_user(buf, sea_of_ones, chunk))
			return -EFAULT;
		buf += chunk;
		todo -= chunk;

		cond_resched(); /* asi by bylo super zjistit co dela tohle */
	}
	return count;
}

static loff_t dev_one_seek(struct file * filp, loff_t offset, int orig)
{
        return filp->f_pos = 0;
}

static struct file_operations fops = {
	.owner = THIS_MODULE,
	.read = dev_one_read,
	.write = dev_one_write,
	.llseek = dev_one_seek
};

static int __init dev_one_init(void)
{
	int res;

	res = alloc_chrdev_region(&device, 0, 1, "dev_one");
	if (res) {
		printk(KERN_ERR "Failed to alloc device number\n");
		goto fail_alloc;
	}

	cdev_init(&cdev, &fops);
	cdev.owner = THIS_MODULE;
	cdev.ops = &fops;

	res = cdev_add(&cdev, device, 1);
	if (res) {
		printk(KERN_ERR "Failed to create cdev\n");
		goto fail_addcdev;
	}

	sea_of_ones = (char *)kmalloc(SEASIZE, GFP_KERNEL);
	if (sea_of_ones == NULL) {
		printk(KERN_ERR "kmalloc failed\n");
		goto fail_kmalloc;
	}
	memset(sea_of_ones, 0xff, SEASIZE);

	printk(KERN_INFO "/dev/one initialized\n");
	return 0;

fail_kmalloc:
	cdev_del(&cdev);
fail_addcdev:
	unregister_chrdev_region(device, 1);	
fail_alloc:
	return res;
}

static void __exit dev_one_cleanup(void)
{
	kfree(sea_of_ones);
	cdev_del(&cdev);
	unregister_chrdev_region(device, 1);
	printk(KERN_INFO "/dev/one says bye bye\n");
}

module_init(dev_one_init);
module_exit(dev_one_cleanup);
