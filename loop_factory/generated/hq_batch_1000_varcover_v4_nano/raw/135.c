int main1(int m,int n,int q){
  int l, i, v, r, d, a, t;

  l=(m%8)+16;
  i=l;
  v=i;
  r=l;
  d=5;
  a=m;
  t=n;

  while (i>0) {
      v = v*2;
      r = r/2;
      v = r*r;
      v = v+r;
      i = i-1;
  }

}
