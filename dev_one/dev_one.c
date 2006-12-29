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

#include <asm/uaccess.h>

MODULE_AUTHOR("b42 <b42@srck.net>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("/dev/one");

static dev_t device;
static struct cdev cdev;
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

static int __init dev_one_init(void)
{
	int res;

	res = alloc_chrdev_region(&device, 0, 1, "dev_one");
	if (res) {
		printk(KERN_ERR "Failed to alloc device number\n");
		goto fail_alloc;
	}

	sea_of_ones = (char *)__get_free_page(GFP_KERNEL);
	if (sea_of_ones == NULL) {
		printk(KERN_ERR "Out of memory! We're all gonna die!\n");
		goto fail_memory;
	}
	memset(sea_of_ones, 0xff, PAGE_SIZE);

	cdev_init(&cdev, &fops);
	cdev.owner = THIS_MODULE;
	cdev.ops = &fops;

	res = cdev_add(&cdev, device, 1);
	if (res) {
		printk(KERN_ERR "Failed to create cdev\n");
		goto fail_addcdev;
	}

	printk(KERN_INFO "/dev/one initialized\n");
	return 0;

fail_addcdev:
	free_page((unsigned long)sea_of_ones);
fail_memory:
	unregister_chrdev_region(device, 1);	
fail_alloc:
	return res;
}

static void __exit dev_one_cleanup(void)
{
	cdev_del(&cdev);
	free_page((unsigned long)sea_of_ones);
	unregister_chrdev_region(device, 1);
	printk(KERN_INFO "/dev/one says bye bye\n");
}

module_init(dev_one_init);
module_exit(dev_one_cleanup);
