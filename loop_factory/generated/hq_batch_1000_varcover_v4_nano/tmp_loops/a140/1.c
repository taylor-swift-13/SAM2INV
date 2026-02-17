int main1(int a,int k,int m,int n){
  int l, i, v, u, z, s, h, t, e;

  l=(n%31)+19;
  i=1;
  v=m;
  u=-5;
  z=2;
  s=n;
  h=k;
  t=i;
  e=i;

  while (i<l) {
      v = v*2;
      u = u+v;
      z = z%2;
      if (i+3<=t+l) {
          s = s%3;
      }
      i = i*2;
  }

}
