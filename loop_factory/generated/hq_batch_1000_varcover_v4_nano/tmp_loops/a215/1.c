int main1(int a,int m,int n,int q){
  int l, i, v, u, e, g, r, b, t, j;

  l=(q%38)+17;
  i=1;
  v=(q%60)+60;
  u=(q%9)+2;
  e=0;
  g=0;
  r=n;
  b=l;
  t=4;
  j=m;

  while (v>u*e+g) {
      if (g==u-1) {
          g = 0;
          e = e+1;
      }
      else {
          g = g+1;
      }
      v = v*2;
      u = u+v;
  }

}
