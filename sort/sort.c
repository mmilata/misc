#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#define MAXNUM 16384
#define CMP_INC "cmp.inc"
#define SWAP_INC "swap.inc"
#define DATA_FILE "sort.dat"

struct sort_stat {
	unsigned long long cmp;
	unsigned long long swap;
	unsigned long long call;
} sys_qsort_stats;

struct sort_fun {
	struct sort_stat (*fun)(int*, unsigned);
	char name[64];
};

inline void swap(int *array, unsigned a, unsigned b)
{
	int t = array[a];
	array[a] = array[b];
	array[b] = t;
}

void rand_array(int *array, unsigned n)
{
	unsigned i;
	srandom(time(NULL));
	for(i = 0; i < n; i++){
		array[i] = random()%(MAXNUM+1);
	}
}

void dump(int *array, unsigned n)
{
	unsigned i;

	for(i=0; i < n; i++){
		printf("%d ", array[i]);
	}
	printf("\n");
}

int check(int *array, unsigned n)
{
	unsigned i;
	for(i=0; i < (n-1); i++){
		if(array[i] > array[i+1])
			return 0;
	}
	return 1;
}

int comp(const void *a, const void *b)
{
	sys_qsort_stats.cmp++;
	if(*(int*)a == *(int*)b){
		return 0;
	}else if(*(int*)a > *(int*)b){
		return 1;
	}else{
		return -1;
	}
}


struct sort_stat bubble(int *array, unsigned n)
{
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };

	unsigned i, j;

	for(i = 0; i < n; i++){
		for(j = (n-1); j > i; j--){
			stats.cmp++;
			if(array[j-1] > array[j]){
				swap(array, j-1, j);
				stats.swap++;
			}
		}
	}

	return stats;
}

struct sort_stat bubble2(int *array, unsigned n)
{
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };

	unsigned i, j, swapped;

	for(i = 0; i < n; i++){
		swapped=0;
		for(j = (n-1); j > i; j--){
			stats.cmp++;
			if(array[j-1] > array[j]){
				swap(array, j-1, j);
				stats.swap++;
				swapped++;
			}
		}
		if(!swapped) break;
	}

	return stats;
}

struct sort_stat selection(int *array, unsigned n)
{
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };
	unsigned i, j, min;

	for(j = 0; j < n-1; j++){
		min = j;
		for(i = j+1; i < n; i++){
			stats.cmp++;
			if(array[i] < array[min])
				min = i;
		}
		swap(array, j, min);
		stats.swap++;
	}

	return stats;
}

struct sort_stat insert(int *array, unsigned n)
{
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };
	unsigned i, j;
	int val;

	for(i = 1; i < n; i++){
		val = array[i];
		j = i;
		while(j > 0 && array[j-1] > val){
			array[j] = array[j-1];
			j--;
			stats.cmp++;
			stats.swap++;
		}
		array[j] = val;
		stats.swap++;
	}

	/* normalne je swap 2x cteni a 2x zapis, zde inkrementujeme swap
	 * pro 1x cteni a 1x zapis ... */
	stats.swap /= 2;
	return stats;
}

struct sort_stat shake(int *array, unsigned n)
{
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };

	unsigned left, right, last, i;

	left = 0;
	right = n-1;

	while(left < right){
		last = right-1;
		for(i=left; i<right; i++){
			stats.cmp++;
			if(array[i] > array[i+1]){
				swap(array, i, i+1);
				last = i;
				stats.swap++;
			}
		}
		right = last;

		last = left+1;
		for(i=right; i>left; i--){
			stats.cmp++;
			if(array[i-1] > array[i]){
				swap(array, i-1, i);
				last = i;
				stats.swap++;
			}
		}
		left = last;
	}

	return stats;
}

struct sort_stat quick(int *array, unsigned n)
{
	struct sort_stat tmp, stats = { .cmp = 0, .swap = 0, .call = 0 };

	if(n > 1){
		unsigned i, ins = 0;

		for(i = 1; i < n; i++){
			stats.cmp++;
			if(array[i] < array[0]){
				swap(array, ++ins, i);
				stats.swap++;
			}
		}
		swap(array, 0, ins);
		stats.swap++;

		tmp = quick(array, ins);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		tmp = quick(array+ins+1, n-ins-1);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		stats.call += 2;
	}

	return stats;
}

struct sort_stat quick2(int *array, unsigned n)
{
	struct sort_stat tmp, stats = { .cmp = 0, .swap = 0, .call = 0 };

	if(n > 1){
		if(n < 7)
			return insert(array, n);

		unsigned i, ins = 0;

		for(i = 1; i < n; i++){
			stats.cmp++;
			if(array[i] < array[0]){
				swap(array, ++ins, i);
				stats.swap++;
			}
		}
		swap(array, 0, ins);
		stats.swap++;

		tmp = quick2(array, ins);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		tmp = quick2(array+ins+1, n-ins-1);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		stats.call += 2;
	}

	return stats;
}

struct sort_stat siftdown(int *array, unsigned size, unsigned item)
{
	unsigned toswap = item;
	struct sort_stat stats = { .cmp = 0, .swap = 0, .call = 0 };

	do {
		item = toswap;

		if((2*item+1 < size) && array[2*item+1] > array[toswap]){
			toswap = 2*item+1;
		}

		if((2*item+2 < size) && array[2*item+2] > array[toswap]){
			toswap = 2*item+2;
		}

		if(toswap != item){
			swap(array, item, toswap);
			stats.swap++;
		}
		stats.cmp += 2;

	} while(toswap != item);

	return stats;
}

struct sort_stat heap(int *array, unsigned n)
{
	struct sort_stat tmp, stats = { .cmp = 0, .swap = 0, .call = 0 };

	int i;
	/* leafy nemusime siftovat */
	for(i = n/2; i>=0; i--){
		tmp = siftdown(array, n, i);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
	}

	for(i = n-1; i>0; i--){
		swap(array, i, 0);
		stats.swap++;

		tmp = siftdown(array, i, 0);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
	}

	return stats;
}

struct sort_stat sys_qsort(int *array, unsigned n)
{
	sys_qsort_stats.cmp = 0;

	qsort(array, n, sizeof(int), comp);

	return sys_qsort_stats;
}

struct sort_stat merge(int *array, unsigned n)
{
	struct sort_stat tmp, stats = { .cmp = 0, .swap = 0, .call = 0 };
	unsigned mid, i = 0;
	unsigned a1, a2, max1, max2;
	int *t;

	if(n > 1){
		mid = n/2;
		tmp = merge(array, mid);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		tmp = merge(array+mid, n-mid);
		stats.cmp += tmp.cmp;
		stats.swap += tmp.swap;
		stats.call += tmp.call;

		a1 = 0;
		a2 = mid;
		max1 = mid;
		max2 = n;
		t = (int*)malloc(n*sizeof(int)); /* O(N) */

		while(a1 < max1 && a2 < max2){
			if(array[a1] < array[a2]){ /* stable? */
				t[i++] = array[a1++];
			}else{
				t[i++] = array[a2++];
			}
			stats.cmp++;
		}

		while(a1 < max1)
			t[i++] = array[a1++];

		while(a2 < max2)
			t[i++] = array[a2++];

		for(i=0; i<n; i++) /* memcpy ... */
			array[i] = t[i];

		free(t);

		stats.swap += n/2;
		stats.call += 2;
	}

	return stats;
}

int main(int argc, char *argv[])
{
	int min, max, step;
	int i, j;
	int *ref, *a;
	struct sort_stat cur;
	FILE *dataf, *cmpf, *swapf;

	struct sort_fun f[] = {
	/*	{ bubble,	"Bubble sort" }, */
		{ bubble2,	"Bubble sort" },
		{ shake,	"Shaker sort" },
		{ selection,	"Selection sort" },
		{ insert,	"Insertion sort" },
		{ heap, 	"Heap sort" },
		{ merge,	"Merge sort" },
		{ quick,	"Quick sort"},
		{ sys_qsort,	"LibC qsort" },
	/*	{ quick2,	"Quick+Insertion sort" }, */
		{ NULL, 	"END" }
	};

	if(argc == 2){

		max = atoi(argv[1]);
		ref = (int*)malloc(max * sizeof(int));
		a = (int*)malloc(max * sizeof(int));
		rand_array(ref, max);

		for(i = 0; f[i].fun != NULL; i++){
			printf("Function: %s\n", f[i].name);
			memcpy(a, ref, max*sizeof(int));
			cur = f[i].fun(a, max);
			printf("Result: %s\n",
				(check(a, max) ? "OK":"b42 fucked up again"));
			printf("Comparsions: %lld\n", cur.cmp);
			printf("Swaps: %lld\n", cur.swap);
			printf("Calls: %lld\n", cur.call);
			printf("\n");
		}
	
	}else if(argc == 4){

		min = atoi(argv[1]);
		max = atoi(argv[2]);
		step = atoi(argv[3]);
		min = (min > 0 ? min : 1);

		if(
			(cmpf = fopen(CMP_INC, "w")) == NULL ||
			(swapf = fopen(SWAP_INC, "w")) == NULL ||
			(dataf = fopen(DATA_FILE, "w")) == NULL
		){
			fprintf(stderr, "Cannot open one of the output files\n");
			perror("fopen");
			exit(EXIT_FAILURE);
		}

		ref = (int*)malloc(max * sizeof(int));
		a = (int*)malloc(max * sizeof(int));
		rand_array(ref, max);

		fprintf(cmpf, "plot\\\n");
		fprintf(swapf, "plot\\\n");
		fprintf(dataf, "#data sets:\n");
		for(i = 0; f[i].fun != NULL; i++){
			fprintf(dataf, "# %d: %s\n", i, f[i].name);

			fprintf(cmpf,
				"  \"%s\" index %d using 1:2 t \"%s\" w lines%s\n",
				DATA_FILE, i, f[i].name,
				(f[i+1].fun ? ",\\" : "\n"));
			fprintf(swapf,
				"  \"%s\" index %d using 1:3 t \"%s\" w lines%s\n",
				DATA_FILE, i, f[i].name,
				(f[i+1].fun ? ",\\" : "\n"));
		}

		for(i = 0; f[i].fun != NULL; i++){
			fprintf(dataf, "\n\n# %d -- %s\n", i, f[i].name);
			fprintf(dataf, "# 1 array size  2 comparsions  3 swaps\n");
			for(j = min; j <= max; j += step){
				memcpy(a, ref, max*sizeof(int));
				cur = f[i].fun(a, j);
				fprintf(dataf, "%d", j);
				if(!check(a, j)){
					fprintf(dataf, "\t42\t42");
					continue;
				}
				fprintf(dataf, "\t%lld\t%lld\n", cur.cmp, cur.swap);
			}
		}

		printf("Data generated, now run 'gnuplot sort.gnuplot' to draw graphs\n");

		fclose(dataf);
		fclose(swapf);
		fclose(cmpf);

	}else{
		printf("%s <num>\n", argv[0]);
		printf("%s <min> <max> <step>\n", argv[0]);
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
} 
