int main1(int k,int n,int p,int q){
  int l, i, v, a, u, z, d;

  l=(n%24)+11;
  i=0;
  v=l;
  a=n;
  u=i;
  z=p;
  d=q;

  while (i<l) {
      v = v+1;
      a = a-1;
      v = v*3;
      a = a/3;
      a = a*2;
      u = v*v;
      v = v%2;
  }

}
