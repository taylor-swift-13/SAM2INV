int main1(){
  int dl, qb, z26, lfm, a, ap;

  dl=(1%35)+15;
  qb=(1%35)+15;
  z26=1;
  lfm=0;
  a=0;
  ap=1;

  while (dl!=qb) {
      if (dl>qb) {
          dl = dl - qb;
          z26 = z26 - lfm;
          a = a - ap;
      }
      else {
          qb -= dl;
          lfm -= z26;
          ap = ap - a;
      }
      z26 = z26*2+5;
  }

}
