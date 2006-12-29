/*
 * /dev/one
 * So the balance of 0's and 1's in the universe can be restored again.
 *
 * by <b42@srck.net> (mostly stolen from mem driver)
 *
 */

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/init.h>
#include <linux/types.h>
#include <linux/fs.h>
#include <linux/errno.h>
#include <linux/cdev.h>
#include <linux/device.h>

#include <asm/uaccess.h>

MODULE_AUTHOR("b42 <b42@srck.net>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("/dev/one");

static dev_t device = MKDEV(0,0);
static struct cdev cdev;
static struct class *class = NULL;
static char * sea_of_ones = NULL;
static int initialized = 0;

static ssize_t dev_one_write(struct file * filp, const char __user * buf,
		      size_t count, loff_t *fpos)
{
	return count;
}

static ssize_t dev_one_read(struct file * filp, char __user * buf,
			    size_t count, loff_t *fpos)
{
	size_t todo = count;

	if(!access_ok(VERIFY_WRITE, buf, count))
		return -EFAULT;

	while (todo) {
		size_t chunk = todo;

		if (chunk > PAGE_SIZE)
			chunk = PAGE_SIZE;
		if (__copy_to_user(buf, sea_of_ones, chunk))
			return -EFAULT;
		buf += chunk;
		todo -= chunk;

		cond_resched(); /* not 100% sure what this does */
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

static void dev_one_cleanup(void)
{
	if (initialized)
		cdev_del(&cdev);
	if (class) {
		class_device_destroy(class,device);
		class_destroy(class);
	}
	if (sea_of_ones)
		free_page((unsigned long)sea_of_ones);
	if (device != MKDEV(0,0))
		unregister_chrdev_region(device, 1);
	printk(KERN_INFO "/dev/one unloaded\n");
}

static int __init dev_one_init(void)
{
	int res;

	res = alloc_chrdev_region(&device, 0, 1, "dev_one");
	if (res) {
		printk(KERN_ERR "Failed to alloc device number\n");
		goto fail;
	}

	sea_of_ones = (char *)__get_free_page(GFP_KERNEL);
	if (sea_of_ones == NULL) {
		printk(KERN_ERR "Out of memory! We're all gonna die!\n");
		res = -ENOMEM;
		goto fail;
	}
	memset(sea_of_ones, 0xff, PAGE_SIZE);

	cdev_init(&cdev, &fops);
	cdev.owner = THIS_MODULE;
	cdev.ops = &fops;

	class = class_create(THIS_MODULE, "dev_one");
	if (IS_ERR(class)) {
		printk(KERN_ERR "Failed to create device class\n");
		res = -PTR_ERR(class);
		goto fail;
	}
	class_device_create(class, NULL, device, NULL, "one");

	res = cdev_add(&cdev, device, 1);
	if (res) {
		printk(KERN_ERR "Failed to create cdev\n");
		goto fail;
	}

	initialized = 1;
	printk(KERN_INFO "/dev/one initialized\n");
	return 0;
fail:
	dev_one_cleanup();
	return res;
}

module_init(dev_one_init);
module_exit(dev_one_cleanup);
