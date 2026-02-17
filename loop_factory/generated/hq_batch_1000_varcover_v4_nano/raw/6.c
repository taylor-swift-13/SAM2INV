int main1(int b,int m,int q){
  int l, i, v, x, y, g, t, f;

  l=52;
  i=0;
  v=b;
  x=i;
  y=m;
  g=1;
  t=q;
  f=m;

  while (i<l) {
      v = v+i;
      x = x*x;
      y = y+v*x;
      if (t*t<=l+5) {
          t = t+x;
      }
      i = i+2;
  }

}
