int main1(){
  int hb, hma, mw, ism, g;
  hb=17;
  hma=0;
  mw=1*4;
  ism=-1;
  g=hma;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= hma <= hb;
  loop invariant ism == hma - 1;
  loop invariant mw == 4 + (hma / 2);
  loop invariant g == 4 * hma + (hma * hma) / 4;
  loop invariant ism == -1 + hma;
  loop invariant 0 <= hma;
  loop invariant hma <= hb;
  loop invariant (mw == 4 + (hma / 2));
  loop invariant (ism == hma - 1);
  loop invariant hma == ism + 1;
  loop invariant mw == 4 + ((ism + 1) / 2);
  loop assigns g, mw, ism, hma;
*/
while (hma < hb) {
      mw = mw + (hma % 2);
      g += mw;
      ism += 1;
      hma++;
  }
}