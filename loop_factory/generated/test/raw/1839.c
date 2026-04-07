int main1(int w){
  int ypw, r, p0, tti;

  ypw=(w%7)+14;
  r=0;
  p0=ypw;
  tti=8;

  while (r < ypw) {
      w += 1;
      r = r + 1;
      tti = tti+(tti%7);
      p0 += p0;
  }

}
