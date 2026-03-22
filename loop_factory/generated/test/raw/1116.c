int main1(){
  int b, bx, pa, dp, xv2g;

  b=1+11;
  bx=3;
  pa=b;
  dp=0;
  xv2g=0;

  while (bx<=b-1) {
      dp = dp + pa;
      pa += bx;
      bx = b;
  }

  while (1) {
      if (!(bx>0)) {
          break;
      }
      xv2g = xv2g + pa;
      pa = pa + xv2g;
      bx = 0;
  }

}
