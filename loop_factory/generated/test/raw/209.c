int main1(int n){
  int fn6, l2g, m, l, yw;

  fn6=50;
  l2g=0;
  m=-1;
  l=0;
  yw=fn6;

  while (m<=fn6-1) {
      l = l + m;
      m++;
      yw = yw + m;
  }

  while (l2g<yw) {
      l = yw-l2g;
      l2g = l2g + 1;
      m += yw;
  }

}
