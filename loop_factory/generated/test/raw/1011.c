int main1(){
  int ms, p, gm2, mn, e6, fli;

  ms=1;
  p=0;
  gm2=28;
  mn=0;
  e6=1;
  fli=0;

  for (; gm2>0&&p<ms; p++) {
      if (gm2<=e6) {
          fli = gm2;
      }
      else {
          fli = e6;
      }
      mn = mn + fli;
      e6 += 1;
      gm2 = gm2 - fli;
  }

}
