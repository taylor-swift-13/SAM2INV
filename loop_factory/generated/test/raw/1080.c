int main1(){
  int xbp, oiba, c9, vyp, ize;

  xbp=1*4;
  oiba=0;
  c9=(1%28)+10;
  vyp=5;
  ize=xbp;

  while (c9>oiba) {
      c9 = c9 - oiba;
      vyp += xbp;
      oiba = oiba + 1;
      vyp = vyp*2+4;
  }

  while (1) {
      if (!(ize>0)) {
          break;
      }
      vyp = vyp+1*1;
      ize -= 1;
      c9 = c9+1*1;
      oiba = oiba+1*1;
      oiba = oiba*oiba+oiba;
  }

}
