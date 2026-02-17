int main1(int a,int b,int m,int q){
  int l, i, v, e, r, k, y, f;

  l=q;
  i=1;
  v=-8;
  e=l;
  r=5;
  k=i;
  y=-5;
  f=b;

  while (i<l) {
      v = v+e;
      e = e+r;
      r = r+4;
      if ((i%4)==0) {
          f = f*v;
      }
      i = i*2;
  }

}
