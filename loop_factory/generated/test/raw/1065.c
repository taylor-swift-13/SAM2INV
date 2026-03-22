int main1(int q){
  int s7e6, ypw, e1, fbz, g;

  s7e6=q+15;
  ypw=s7e6;
  e1=0;
  fbz=s7e6;
  g=2;

  while (e1<=s7e6-1) {
      fbz = e1;
      e1 = e1 + 10;
      q = q+s7e6-ypw;
  }

  while (e1<ypw) {
      g = g + q;
      e1 = e1 + 1;
      q += ypw;
  }

}
