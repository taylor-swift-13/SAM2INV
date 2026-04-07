int main1(){
  int d, xh, br, m, hg;

  d=1;
  xh=d;
  br=d;
  m=10;
  hg=d;

  while (1) {
      if (hg>d) {
          break;
      }
      xh += br;
      br = br + m;
      m += 6;
      hg = hg + 1;
  }

}
