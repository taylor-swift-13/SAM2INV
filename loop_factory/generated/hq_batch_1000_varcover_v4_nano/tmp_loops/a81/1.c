int main1(int a,int b,int n,int p){
  int l, i, v, c, m, k, f;

  l=n+5;
  i=l;
  v=i;
  c=p;
  m=n;
  k=i;
  f=6;

  while (i>0) {
      v = v+i;
      c = c*c;
      m = m+v*c;
      v = v*2;
      k = c+i;
      v = v*c;
      i = i/2;
  }

}
