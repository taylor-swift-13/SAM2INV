int main1(int a,int b,int m,int n){
  int l, i, v, q, p, t, z;

  l=21;
  i=l;
  v=-8;
  q=8;
  p=2;
  t=n;
  z=m;

  while (i>0) {
      v = v*2+1;
      q = q*v+1;
      if ((i%3)==0) {
          z = z*2;
      }
      p = p*z;
      t = t*v;
      v = v*2;
      p = p*2;
      i = i/2;
  }

}
