int main1(int a,int b,int n,int p){
  int l, i, v, t, y, r, m, h, x;

  l=a;
  i=1;
  v=6;
  t=a;
  y=a;
  r=n;
  m=p;
  h=8;
  x=-1;

  while (i<l) {
      v = v*2;
      t = t/2;
      if (m+5<l) {
          h = h%9;
      }
      else {
          t = t*m;
      }
      v = x*x;
      i = i*3;
  }

}
