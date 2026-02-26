int main85(int k,int p,int q){
  int n, o, d;

  n=k;
  o=n;
  d=1;

  while (o-1>=0) {
      if (d+2<n) {
          d = d+o;
      }
      if (k*k<=n+2) {
          d = d*d;
      }
      o = o-1;
  }

  while (d-4>=0) {
      n = n+2;
      n = n*n;
      if ((d%9)==0) {
          n = n*2;
      }
      else {
          n = n*n;
      }
      n = n*n;
  }

  while (o<=n-1) {
      d = d+2;
      d = d*2;
  }

}
