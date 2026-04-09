int main1(int n){
  int gn, f, d, pa, ma0;

  gn=n+5;
  f=0;
  d=0;
  pa=0;
  ma0=16;

  while (f < gn) {
      pa = 1 - pa;
      f = f + 1;
      d = d + ma0 * (2 * pa - 1);
      ma0 += f;
  }

}
