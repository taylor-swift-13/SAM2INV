int main1(){
  int d0, c9, uxv, x, cgv, d;

  d0=1+19;
  c9=d0;
  uxv=(1%40)+2;
  x=0;
  cgv=-6;
  d=c9;

  while (uxv!=x) {
      x = uxv;
      uxv = (uxv+d0/uxv)/2;
      d = d+x-uxv;
  }

  while (1) {
      if (!(c9*2<=cgv)) {
          break;
      }
      uxv += d;
      d += d;
      c9 = c9*2;
  }

}
