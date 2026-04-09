int main1(){
  int w, td4, rmt, xr, qfq;

  w=29;
  td4=0;
  rmt=1;
  xr=0;
  qfq=0;

  while (1) {
      if (!(td4 < w)) {
          break;
      }
      rmt = rmt * xr;
      qfq = qfq + rmt;
      xr = xr + w;
      td4++;
  }

}
