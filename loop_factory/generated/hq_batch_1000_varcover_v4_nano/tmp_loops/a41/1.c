int main1(int b,int k,int n,int p){
  int l, i, v, g, e, c, t, s;

  l=67;
  i=l;
  v=b;
  g=n;
  e=k;
  c=i;
  t=-5;
  s=n;

  while (i>0) {
      v = v+i;
      g = g*g;
      e = e+v*g;
      v = v*2;
      if (i+5<=b+l) {
          c = k*g;
      }
      e = e*e+v;
      i = i-1;
  }

}
