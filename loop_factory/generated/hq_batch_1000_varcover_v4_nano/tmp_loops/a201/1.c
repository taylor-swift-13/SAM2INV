int main1(int a,int b,int m,int q){
  int l, i, v, p, c, x, d, r, f, n;

  l=a+16;
  i=0;
  v=6;
  p=a;
  c=l;
  x=l;
  d=-8;
  r=b;
  f=b;
  n=3;

  while (i<l) {
      if (i<l/2) {
          v = v+p;
      }
      else {
          v = v*p;
      }
      x = x*x+v;
      v = v%5;
      p = v*v;
      x = x*x+p;
  }

}
