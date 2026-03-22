int main1(int y){
  int hw, j, lbw, re, oiea, g4, jp;

  hw=y;
  j=hw;
  lbw=0;
  re=1;
  oiea=1;
  g4=hw;
  jp=16;

  while (1) {
      if (!(re<=hw)) {
          break;
      }
      oiea += 2;
      lbw++;
      g4 += j;
      re += oiea;
      g4 += jp;
      jp = jp + y;
  }

}
