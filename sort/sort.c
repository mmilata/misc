#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#define MAXNUM 16384

struct sort_stat {
	unsigned long long cmp;
	unsigned long long swap;
	unsigned long long call;
};

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
	//leafy nemusime siftovat
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

int main(int argc, char *argv[])
{
	int min, max, step;
	int i, j;
	int *ref, *a;
	struct sort_stat cur;

	struct sort_fun f[] = {
		{ bubble,	"bubble sort" },
		{ bubble2,	"bubble sort, swap check" },
		{ shake,	"shaker sort" },
		{ quick,	"quick sort, inplace partition, dumb pivot"},
		{ heap, 	"heap sort" },
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

		ref = (int*)malloc(max * sizeof(int));
		a = (int*)malloc(max * sizeof(int));
		rand_array(ref, max);

		printf("#data sets:\n");
		for(i = 0; f[i].fun != NULL; i++){
			printf("# %d: %s\n", i, f[i].name);
		}

		for(i = 0; f[i].fun != NULL; i++){
			printf("\n\n# %d -- %s\n", i, f[i].name);
			printf("# 1 array size  2 comparsions  3 swaps\n");
			for(j = min; j <= max; j += step){
				memcpy(a, ref, max*sizeof(int));
				cur = f[i].fun(a, j);
				printf("%d", j);
				if(!check(a, j)){
					printf("\t42\t42");
					continue;
				}
				printf("\t%lld\t%lld\n", cur.cmp, cur.swap);
			}
		}

		/*
		for(j = min; j <= max; j += step){
			printf("%d", j);
			for(i = 0; f[i].fun != NULL; i++){
				memcpy(a, ref, max*sizeof(int));
				cur = f[i].fun(a, j);
				if(!check(a, j)){
					printf("\t42");
					continue;
				}
				printf("\t%lld", cur.cmp);
			}
			printf("\n");
		}
		*/

	}else{
		printf("%s <num>\n", argv[0]);
		printf("%s <min> <max> <step>\n", argv[0]);
		return 1;
	}

	return 0;
} 
