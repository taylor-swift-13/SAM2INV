int main1(int k,int n,int p,int q){
  int l, i, v, d, a, b, e, g, o;

  l=p+15;
  i=0;
  v=-1;
  d=2;
  a=n;
  b=n;
  e=k;
  g=l;
  o=k;

  while (i<l) {
      b = b*b+v;
      v = v%8;
      o = l*q;
      g = g*2;
      o = o*g;
      g = o*o;
      i = i+2;
  }

}
