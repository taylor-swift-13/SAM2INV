int main2(int b,int p,int q){
  int t, k, v, x, m;

  t=9;
  k=t+2;
  v=b;
  x=b;
  m=b;

  while (k>t) {
      v = v*2+4;
      x = x*v+4;
  }

  while (x<=m/3) {
      x = x*3;
      while (t<x) {
          v = v+1;
          m = m+v*v*v*v;
      }
  }

}
