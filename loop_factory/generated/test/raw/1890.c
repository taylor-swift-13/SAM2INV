int main1(int x,int g){
  int xt, yg, qnvd, xo, eq, mf, jp, dwg, j;

  xt=g+17;
  yg=xt;
  qnvd=8;
  xo=yg;
  eq=yg;
  mf=-4;
  jp=g;
  dwg=xt;
  j=x;

  while (1) {
      if (!(yg-1>=0)) {
          break;
      }
      if (yg<xt/2) {
          qnvd = qnvd + xo;
      }
      else {
          qnvd = qnvd + 1;
      }
      if ((yg%8)==0) {
          j += yg;
      }
      dwg = dwg + qnvd;
      mf = mf + qnvd;
      jp = xo+eq+mf;
      xo = xo + 1;
      j += yg;
      g = jp-g;
      mf += yg;
      yg += 1;
  }

}
