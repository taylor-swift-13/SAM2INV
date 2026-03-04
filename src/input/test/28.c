int main28(int k,int m,int p){
  int c, g, n;

  c=p+16;
  g=1;
  n=1;

  while (1) {
      if (n==1) {
          n = 2;
      }
      else {
          if (n==2) {
              n = 1;
          }
      }
  }

  while (c<=g-1) {
      if (p<m+3) {
          n = n+1;
      }
      c = c+1;
  }

}
