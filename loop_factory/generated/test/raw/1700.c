int main1(){
  int hb, hma, mw, ism, g;

  hb=17;
  hma=0;
  mw=1*4;
  ism=-1;
  g=hma;

  while (hma < hb) {
      mw = mw + (hma % 2);
      g += mw;
      ism += 1;
      hma++;
  }

}
