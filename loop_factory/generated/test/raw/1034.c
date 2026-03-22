int main1(){
  int dwv, x, xqe, jh, sj;

  dwv=1*3;
  x=0;
  xqe=0;
  jh=0;
  sj=2;

  while (xqe<dwv) {
      jh += xqe;
      xqe++;
      sj += jh;
  }

  while (dwv<xqe) {
      x = xqe-dwv;
      sj += jh;
      dwv++;
  }

}
