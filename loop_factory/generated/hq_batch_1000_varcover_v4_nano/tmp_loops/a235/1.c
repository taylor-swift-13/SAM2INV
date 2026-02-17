int main1(int k,int m,int n,int p){
  int l, i, v, u, r, s, t;

  l=m;
  i=1;
  v=1;
  u=4;
  r=1;
  s=-8;
  t=n;

  while (i<l) {
      v = v+i;
      u = u*u;
      r = r+v*u;
      t = t*s;
      i = i*2;
  }

}
