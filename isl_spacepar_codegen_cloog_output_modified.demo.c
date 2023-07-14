int min(int x, int y) { return x < y ? x : y; }
int max(int x, int y) { return x > y ? x : y; }
void calculate()
{
int X[100][100];
int Y[100][100];
int i, j, p;
X[1][100] = X[1][100] + Y[1 -1][100];
for (p=-99;p<=98;p++) {
  if (p >= 0) {
    Y[(p+1)][1] = X[(p+1)][1 -1] + Y[(p+1)][1];
  }
  for (i=max(1,p+2);i<=min(100,p+100);i++) {
    X[i][(-p+i-1)] = X[i][(-p+i-1)] + Y[i-1][(-p+i-1)];
    Y[i][(-p+i)] = X[i][(-p+i)-1] + Y[i][(-p+i)];
  }
  if (p <= -1) {
    X[(p+101)][100] = X[(p+101)][100] + Y[(p+101)-1][100];
  }
}
Y[100][1] = X[100][1 -1] + Y[100][1];
}
