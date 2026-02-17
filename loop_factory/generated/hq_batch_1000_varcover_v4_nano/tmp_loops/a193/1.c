int main1(int a,int k,int m,int p){
  int l, i, v, b, c, e, d, q, j, y;

  l=p;
  i=0;
  v=k;
  b=2;
  c=-4;
  e=l;
  d=i;
  q=-6;
  j=2;
  y=1;

  while (i<l) {
      if (i<l/2) {
          v = v+b;
      }
      else {
          v = v*b;
      }
      e = e*e+v;
      v = v%4;
      if (i+2<=m+l) {
          v = v*2;
      }
      else {
          v = v*d;
      }
  }

}
