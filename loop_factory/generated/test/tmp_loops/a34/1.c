int main1(){
  int r, iaz, hb, ln1, e7zt, ahm, e, fkc, a4, s8v4;

  r=(1%17)+13;
  iaz=r;
  hb=3;
  ln1=0;
  e7zt=0;
  ahm=5;
  e=iaz;
  fkc=r;
  a4=r;
  s8v4=5;

  while (iaz<r) {
      e7zt++;
      ln1 = ln1 + 1;
      if (ln1>=7) {
          ln1 = ln1 - 7;
          hb++;
      }
      iaz = iaz + 1;
      if (iaz+1<=a4+r) {
          a4 += iaz;
      }
      ahm = ahm+r-iaz;
      s8v4 = s8v4 + 3;
      e += ahm;
      a4 = ahm+e+fkc;
      ahm++;
  }

}
