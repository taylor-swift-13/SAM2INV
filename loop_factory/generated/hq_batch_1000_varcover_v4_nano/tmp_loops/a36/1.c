int main1(int a,int k,int m,int p){
  int l, i, v, t, r, h, j, e;

  l=21;
  i=0;
  v=l;
  t=a;
  r=l;
  h=i;
  j=m;
  e=-2;

  while (i<l) {
      v = v+i;
      t = t*t;
      r = r+v*t;
      if ((i%4)==0) {
          v = v%4;
      }
      if (v+4<l) {
          r = r*r+t;
      }
      else {
          e = e%2;
      }
      i = i+3;
  }

}
