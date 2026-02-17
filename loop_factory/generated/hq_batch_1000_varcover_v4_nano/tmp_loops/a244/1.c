int main1(int a,int k,int m,int q){
  int l, i, v, x, f, u, s, g, b, c;

  l=(k%19)+18;
  i=1;
  v=m;
  x=2;
  f=i;
  u=m;
  s=l;
  g=-2;
  b=k;
  c=-5;

  while (i<l) {
      v = v*4+4;
      x = x*v+4;
      x = x*u;
      b = b*2;
      c = b*b;
      f = f*x;
      g = g%4;
      i = i*3;
  }

}
