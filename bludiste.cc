#include <vector>
#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <ctime>
#include <queue>
#include <map>

#define MAX_SIZE 256
#define INV "\033[7m"
#define RED "\033[0;31m"
#define NORMAL "\033[0m"
#define GREEN "\033[32m"
#define BLUE "\033[0;34m"
#define SLEEPTIME 20000

using namespace std;

bool bludiste[MAX_SIZE][MAX_SIZE];
int dist[MAX_SIZE][MAX_SIZE];
int bfs_pred_x[MAX_SIZE][MAX_SIZE];
int bfs_pred_y[MAX_SIZE][MAX_SIZE];
int cil_x[3];
int cil_y[3];
int truecil_x;
int truecil_y;
bool path[MAX_SIZE][MAX_SIZE];
bool beenhere[MAX_SIZE][MAX_SIZE];

void nuluj(void)
{
	for(int i = 0; i < MAX_SIZE; i++)
		for(int j = 0; j < MAX_SIZE; j++){
			bludiste[i][j] = false;
			dist[i][j] = -1;
			path[i][j] = 0;
			beenhere[i][j] = 0;
		}
}

void nuluj_path(void)
{
	for(int i = 0; i<MAX_SIZE; i++)
		for(int j = 0; j<MAX_SIZE; j++){
			path[i][j] = false;
		}
}
void nuluj_bfs(void)
{
	for(int i = 0; i < MAX_SIZE; i++)
		for(int j = 0; j < MAX_SIZE; j++){
			dist[i][j] = -1;
			bfs_pred_x[i][j] = 0;
			bfs_pred_y[i][j] = 0;
		}
}

void vykresli(int x, int y, int s_x, int s_y)
{
	printf(INV " ");
	for(int i = 0; i < x; i++)
		printf(" ");
	printf(" \n" NORMAL);
	for(int i = 0; i < y; i++){
		printf(INV " " NORMAL);
		for(int j = 0; j < x; j++){
			if(path[j][i]){
				printf(GREEN INV " " NORMAL);
			}else if(beenhere[j][i]){
				printf(BLUE INV " " NORMAL);
			}else if(bludiste[j][i]){
				printf(INV " " NORMAL);
			}else{
				if(s_x == j && s_y == i){
					printf(RED "S" NORMAL);
				}else if(cil_x[0] == j && cil_y[0] == i){
					printf(RED "A" NORMAL);
				}else if(cil_x[1] == j && cil_y[1] == i){
					printf(RED "C" NORMAL);
				}else if(cil_x[2] == j && cil_y[2] == i){
					printf(RED "B" NORMAL);
				}else{
					printf(NORMAL " "); //normal
				}
			}
		}
		printf(INV " \n" NORMAL);
	}
	printf(INV " ");
	for(int i = 0; i < x; i++)
		printf(" ");
	printf(" \n\n" NORMAL);
}

void nahodne(void)
{
	for(int i = 0; i<MAX_SIZE; i++){
		for(int j = 0; j<MAX_SIZE; j++){
			bludiste[i][j] = rand() % 2;
		}
	}
}

void bfs(int s_x, int s_y, int max_x, int max_y)
{
	queue<pair<int,int> > q;
	q.push(make_pair(s_x, s_y));
	dist[s_x][s_y] = 0;

	while(!q.empty()){
		pair<int,int> c = q.front();
		q.pop();
		int x = c.first;
		int y = c.second;
		
		if(x > 0 && dist[x-1][y] == -1 && !bludiste[x-1][y]){ //doleva
			dist[x-1][y] = dist[x][y]+1;
			q.push(make_pair(x-1,y));
		}
		if(y > 0 && dist[x][y-1] == -1 && !bludiste[x][y-1]){ //nahoru
			dist[x][y-1] = dist[x][y]+1;
			q.push(make_pair(x,y-1));
		}
		if(x+1 < max_x && dist[x+1][y] == -1 && !bludiste[x+1][y]){ //doprava
			dist[x+1][y] = dist[x][y]+1;
			q.push(make_pair(x+1,y));
		}
		if(y+1 < max_y && dist[x][y+1] == -1 && !bludiste[x][y+1]){ //dolu
			dist[x][y+1] = dist[x][y]+1;
			q.push(make_pair(x,y+1));
		}

	}
}

bool find_path1(int s_x, int s_y, int c_x, int c_y, int max_x, int max_y)
{
	if(s_x == c_x && s_y == c_y){
		path[s_x][s_y] = true;
		return true;
	}
	if(beenhere[s_x][s_y] || bludiste[s_x][s_y] || s_x < 0 || s_y < 0 || s_x >= max_x || s_y >= max_y)
		return false;

	beenhere[s_x][s_y] = true;
	path[s_x][s_y] = true;

	vykresli(max_x, max_y, -1, -1);
	usleep(SLEEPTIME);

	bool result = find_path1(s_x,s_y-1,c_x,c_y,max_x,max_y)
		   || find_path1(s_x,s_y+1,c_x,c_y,max_x,max_y)
		   || find_path1(s_x-1,s_y,c_x,c_y,max_x,max_y)
		   || find_path1(s_x+1,s_y,c_x,c_y,max_x,max_y);

	if(!result)
		path[s_x][s_y] = false;

	return result;
}

bool find_path4(int s_x, int s_y, int c_x, int c_y, int max_x, int max_y)
{
	nuluj_bfs();
	queue<pair<int,int> > q;
	q.push(make_pair(s_x, s_y));
	dist[s_x][s_y] = 0;
	bfs_pred_x[s_x][s_y] = s_x;
	bfs_pred_y[s_x][s_y] = s_y;

	while(!q.empty()){
		pair<int,int> c = q.front();
		q.pop();
		int x = c.first;
		int y = c.second;

		beenhere[x][y] = true;

		nuluj_path();
		int my_x = x;
		int my_y = y;
		path[my_x][my_y] = true;
		while(my_x != s_x || my_y != s_y){
			int oldx = my_x;
			my_x = bfs_pred_x[my_x][my_y];
			my_y = bfs_pred_y[oldx][my_y];
			path[my_x][my_y] = true;
		}

		vykresli(max_x, max_y, -1, -1);

		if(x == c_x && y == c_y)
			break;

		usleep(SLEEPTIME);

		if(x > 0 && dist[x-1][y] == -1 && !bludiste[x-1][y]){ //doleva
			dist[x-1][y] = dist[x][y]+1;
			bfs_pred_x[x-1][y] = x;
			bfs_pred_y[x-1][y] = y;
			q.push(make_pair(x-1,y));
		}
		if(y > 0 && dist[x][y-1] == -1 && !bludiste[x][y-1]){ //nahoru
			dist[x][y-1] = dist[x][y]+1;
			bfs_pred_x[x][y-1] = x;
			bfs_pred_y[x][y-1] = y;
			q.push(make_pair(x,y-1));
		}
		if(x+1 < max_x && dist[x+1][y] == -1 && !bludiste[x+1][y]){ //doprava
			dist[x+1][y] = dist[x][y]+1;
			bfs_pred_x[x+1][y] = x;
			bfs_pred_y[x+1][y] = y;
			q.push(make_pair(x+1,y));
		}
		if(y+1 < max_y && dist[x][y+1] == -1 && !bludiste[x][y+1]){ //dolu
			dist[x][y+1] = dist[x][y]+1;
			bfs_pred_x[x][y+1] = x;
			bfs_pred_y[x][y+1] = y;
			q.push(make_pair(x,y+1));
		}
	}

	return true;
}

bool find_path2(int s_x, int s_y, int c_x, int c_y, int max_x, int max_y)
{
	if(s_x == c_x && s_y == c_y){
		path[s_x][s_y] = true;
		return true;
	}
	if(beenhere[s_x][s_y] || bludiste[s_x][s_y] || s_x < 0 || s_y < 0 || s_x >= max_x || s_y >= max_y)
		return false;

	beenhere[s_x][s_y] = true;
	path[s_x][s_y] = true;

	vykresli(max_x, max_y, -1, -1);
	usleep(20000);
	
	bool result;

	if(s_x > c_x){ //doleva dolu doprava nahoru
		result = find_path2(s_x-1,s_y,c_x,c_y,max_x,max_y)
			   || find_path2(s_x,s_y+1,c_x,c_y,max_x,max_y)
			   || find_path2(s_x+1,s_y,c_x,c_y,max_x,max_y)
			   || find_path2(s_x,s_y-1,c_x,c_y,max_x,max_y);
	}else if(s_x < c_x){ //doprava dolu doleva nahoru
		result = find_path2(s_x+1,s_y,c_x,c_y,max_x,max_y)
			   || find_path2(s_x,s_y+1,c_x,c_y,max_x,max_y)
			   || find_path2(s_x-1,s_y,c_x,c_y,max_x,max_y)
			   || find_path2(s_x,s_y-1,c_x,c_y,max_x,max_y);
	}else{ //dolu nahoru doleva doprav
		result = find_path2(s_x,s_y-1,c_x,c_y,max_x,max_y)
			   || find_path2(s_x,s_y+1,c_x,c_y,max_x,max_y)
			   || find_path2(s_x-1,s_y,c_x,c_y,max_x,max_y)
			   || find_path2(s_x+1,s_y,c_x,c_y,max_x,max_y);
	}

	if(!result)
		path[s_x][s_y] = false;

	return result;
}

bool find_path3(int s_x, int s_y, int c_x, int c_y, int max_x, int max_y)
{
	//if(c_x == truecil_x && c_y == truecil_y){
		nuluj_bfs();
		bfs(c_x, c_y, max_x, max_y);
	//}
	if(s_x == c_x && s_y == c_y){
		path[s_x][s_y] = true;
		return true;
	}
	if(beenhere[s_x][s_y] || bludiste[s_x][s_y] || s_x < 0 || s_y < 0 || s_x >= max_x || s_y >= max_y)
		return false;

	beenhere[s_x][s_y] = true;
	path[s_x][s_y] = true;

	vykresli(max_x, max_y, -1, -1);
	usleep(20000);
	
	bool result;

	printf("%d\n", dist[s_x][s_y]);
	if(s_x > 0 && dist[s_x-1][s_y] < dist[s_x][s_y]){
		result = find_path3(s_x-1,s_y,c_x,c_y,max_x,max_y);
	}else if(s_y > 0 && dist[s_x][s_y-1] < dist[s_x][s_y]){
		result = find_path3(s_x,s_y-1,c_x,c_y,max_x,max_y);
	}else if(s_x < MAX_SIZE-1 && dist[s_x+1][s_y] < dist[s_x][s_y]){
		result = find_path3(s_x+1,s_y,c_x,c_y,max_x,max_y);
	}else{
		result = find_path3(s_x,s_y+1,c_x,c_y,max_x,max_y);
	}
	if(!result)
		result = find_path3(s_x-1,s_y,c_x,c_y,max_x,max_y)
			|| find_path3(s_x+1,s_y,c_x,c_y,max_x,max_y)
			|| find_path3(s_x,s_y-1,c_x,c_y,max_x,max_y);

	if(!result)
		path[s_x][s_y] = false;

	return result;
}

void tri_nejvzdalenejsi(int x, int y, int s_x, int s_y, int& x1, int& y1, int& x2, int& y2, int& x3, int& y3)
{
	//bfs(s_x, s_y, x, y);
	cil_y[0] = cil_y[1] = cil_y[2] = y-1;

	for(int i = 0; i<x; i++){
		if(!bludiste[i][y-1]){
			cil_x[0] = i;
			break;
		}
	}

	for(int i = x-1; i >= 0; i--){
		if(!bludiste[i][y-1]){
			cil_x[1] = i;
			break;
		}
	}

	for(int i = (int)(x/(2.5)); i<x; i++){
		if(!bludiste[i][y-1]){
			cil_x[2] = i;
			break;
		}
	}
}

void vytvor_bludiste(int x, int y)
{
	for(int i = 1; i<x-1; i+=2){
		for(int j = 1; j<y-1; j+=2){
			bludiste[i][j] = true;

			int smer = rand() % 4;
			switch(smer){
				case 0: //nahoru
					if(!bludiste[i][j-1]){
						bludiste[i][j-1] = true;
						break;
					}
				case 1: //doleva
					if(!bludiste[i-1][j]){
						bludiste[i-1][j] = true;
						break;
					}
				case 2: //dolu
					if(!bludiste[i][j+1]){
						bludiste[i][j+1] = true;
						break;
					}
				case 3: //doprava
					if(!bludiste[i+1][j]){
						bludiste[i+1][j] = true;
						break;
					}
				default:
					//printf("%d %d\n", i, j);
					j-=2;
			}
		}
	}

	if(x % 2 == 0){
		for(int i = 1; i < y; i+=2){
			bludiste[x-1][i] = true;
			int smer = rand() % 4;
			switch(smer){
				case 0: //nahoru
					if(!bludiste[x-1][i-1]){
						bludiste[x-1][i-1] = true;
						break;
					}
				case 1: //dolu
					if(!bludiste[x-1][i+1]){
						bludiste[x-1][i+1] = true;
						break;
					}
				default:
					break;
			}
		}
	}

	if(y % 2 == 0){
		for(int i = 1; i < x; i+= 2){
			bludiste[i][y-1] = true;
			int smer = rand() % 4;
			switch(smer){
				case 0: //doleva
					if(!bludiste[i-1][y-1]){
						bludiste[i-1][y-1] = true;
						break;
					}
				case 1: //doleva
					if(!bludiste[i+1][y-1]){
						bludiste[i+1][y-1] = true;
						break;
					}
				default:
					break;
			}
		}
	}
}

void nahodna_zed(int x, int y, int& z_x, int& z_y)
{
	do{
		z_x = (rand() % x);
		z_y = (rand() % y);
	}while((z_x % 2 == 0 && z_y % 2 == 0) || bludiste[z_x][z_y]);

	bludiste[z_x][z_y] = true;
}

int main(int argc, char *argv[])
{
	int seed = 0;
	bool (*fun)(int, int, int, int, int, int) = find_path1;

	if(argc >= 5){
		seed = atoi(argv[4]);
	}
	if(argc >= 4){
		if(!strcmp("bfs", argv[3])){
			fun = find_path4;
		}else{
			fun = find_path1;
		}
	}
	if(argc < 3){
		printf("program x y [dfs|bfs] [randomseed]\n");
		return 1;
	}

	int x = atoi(argv[1]);
	int y = atoi(argv[2]);
	int x1, x2, x3, y1, y2, y3;
	int start_x, start_y;

	nuluj();
	seed = (seed ? seed : time(NULL));
	srand(seed);

	vytvor_bludiste(x, y);

	do{
		start_x = rand() % x;
		start_y = 0;
	}while(bludiste[start_x][start_y]);

	tri_nejvzdalenejsi(x, y, start_x, start_y, x1, y1, x2, y2, x3, y3);

	int notdead = (x*y)/4;
	while(notdead--){
		int z_x, z_y;
		int reachable = 0;

		nahodna_zed(x,y,z_x,z_y);
		bfs(start_x,start_y,x,y);

		if(dist[cil_x[0]][cil_y[0]] != -1)
			reachable++;
		if(dist[cil_x[1]][cil_y[1]] != -1)
			reachable++;
		if(dist[cil_x[2]][cil_y[2]] != -1)
			reachable++;

		if(reachable == 1)
			break;

		if(reachable == 0){
			bludiste[z_x][z_y] = false;
		}
		
		nuluj_bfs();
		printf(".\n");
	}

	if(!notdead){
		printf("sorry, we're fscked\n");
		return 1;
	}

	for(int i=0; i<3; i++){
		if(dist[cil_x[i]][cil_y[i]] != -1){
			truecil_x = cil_x[i];
			truecil_y = cil_y[i];
		}
	}

	fun(start_x, start_y, truecil_x, truecil_y, x, y);

	vykresli(x,y,start_x,start_y);
	printf("\033[0m\nseed: %d\n", seed);
}
