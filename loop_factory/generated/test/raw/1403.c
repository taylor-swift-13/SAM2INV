int main1(int s,int d){
  int i1m, xt, yh, xbmy, jj;

  i1m=62;
  xt=0;
  yh=3;
  xbmy=16;
  jj=6;

  while (1) {
      if (jj>i1m) {
          break;
      }
      xt = xt + yh;
      yh += xbmy;
      jj += 1;
      xbmy += 6;
      s = s+yh+xt;
  }

}
