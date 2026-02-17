int main1(int k,int m,int p,int q){
  int l, i, v, n, a, y, x;

  l=p;
  i=l;
  v=8;
  n=k;
  a=0;
  y=-2;
  x=3;

  while (i>0) {
      v = v*2;
      n = n+v;
      a = a%8;
      if (i+6<=k+l) {
          v = v*a;
      }
      a = v*v;
      i = i/2;
  }

}
