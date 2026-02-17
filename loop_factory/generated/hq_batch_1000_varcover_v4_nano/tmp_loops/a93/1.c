int main1(int b,int m,int n,int p){
  int l, i, v, r, e, c, z, d;

  l=(m%39)+19;
  i=0;
  v=0;
  r=p;
  e=n;
  c=l;
  z=l;
  d=p;

  while (i<l) {
      v = v*2;
      r = r/2;
      z = z*2;
      if (d+2<l) {
          e = d*d;
      }
      else {
          v = e*e;
      }
      c = c%9;
      i = i+3;
  }

}
