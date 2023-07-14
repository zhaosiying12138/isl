#define S1(i,j) X[i][j] = X[i][j] + Y[i-1][j]
#define S2(i,j) Y[i][j] = X[i][j-1] + Y[i][j]

int min(int x, int y) { return x < y ? x : y; }
int max(int x, int y) { return x > y ? x : y; }

void calculate()
{
int X[100][100];
int Y[100][100];
int i, j, p;
S1(1,100);
for (p=-99;p<=98;p++) {
  if (p >= 0) {
    S2((p+1),1);
  }
  for (i=max(1,p+2);i<=min(100,p+100);i++) {
    S1(i,(-p+i-1));
    S2(i,(-p+i));
  }
  if (p <= -1) {
    S1((p+101),100);
  }
}
S2(100,1);
}
