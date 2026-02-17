int main1(int a,int b,int k,int m){
  int l, i, v, d, r, t, z, q, p;

  l=(k%8)+17;
  i=l;
  v=m;
  d=i;
  r=k;
  t=4;
  z=b;
  q=a;
  p=b;

  while (i>0) {
      v = v*2;
      d = d+v;
      r = r%4;
      p = p+v;
      r = r*2;
      if (p+4<l) {
          d = d*d+z;
      }
      if (i+1<=p+l) {
          r = d*d;
      }
      i = i/2;
  }

}
