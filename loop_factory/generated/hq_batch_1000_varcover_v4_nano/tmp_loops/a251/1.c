int main1(int b,int k,int p,int q){
  int l, i, v, f, u, n, s, g, x, o;

  l=(q%28)+5;
  i=l;
  v=p;
  f=p;
  u=-2;
  n=p;
  s=q;
  g=i;
  x=4;
  o=l;

  while (i>0) {
      v = v*2;
      f = f+v;
      u = u%8;
      if ((i%7)==0) {
          f = f*f+x;
      }
      else {
          s = s%8;
      }
      if (o*o<=l+6) {
          g = g*g+f;
      }
      if (i+2<=b+l) {
          x = g*g;
      }
      i = i-1;
  }

}
