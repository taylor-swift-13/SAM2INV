int main1(int a,int m,int n,int q){
  int l, i, v, y, p, t;

  l=(m%37)+11;
  i=0;
  v=-4;
  y=2;
  p=2;
  t=m;

  while (i<l) {
      v = v*4;
      y = y/4;
      t = t*v;
      if (i+2<=a+l) {
          t = t*t+y;
      }
      else {
          y = y*y+p;
      }
      p = p+y;
      p = p*2;
      i = i+1;
  }

}
