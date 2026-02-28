int main180(int b,int p,int q){
  int y, k, n;

  y=52;
  k=y;
  n=y;

  while (k>0) {
      n = n+2;
      n = n%5;
      if (n+5<y) {
          n = n*n;
      }
      n = n*n;
  }

}
