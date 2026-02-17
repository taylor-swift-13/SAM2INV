int main1(int k,int m,int n,int q){
  int l, i, v, s, p, b, u, d, f, x;

  l=n;
  i=l;
  v=8;
  s=k;
  p=q;
  b=n;
  u=m;
  d=m;
  f=l;
  x=n;

  while (i>0) {
      b = b*b+v;
      v = v%9;
      d = d*d+u;
      f = f*2;
      i = i/2;
  }

}
