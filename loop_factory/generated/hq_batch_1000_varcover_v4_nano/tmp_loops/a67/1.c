int main1(int a,int b,int m,int n){
  int l, i, v, p, q, h, y;

  l=n+20;
  i=1;
  v=2;
  p=l;
  q=m;
  h=m;
  y=l;

  while (i<l) {
      v = v*3;
      p = p/3;
      y = y%3;
      y = y%9;
      i = i*2;
  }

}
