int main1(){
  int od, hy, ak, l, wa4, xae8, gp6;

  od=0;
  hy=(1%35)+15;
  ak=(1%35)+15;
  l=1;
  wa4=0;
  xae8=0;
  gp6=1;

  while (hy!=ak) {
      if (hy>ak) {
          hy -= ak;
          l -= wa4;
          xae8 = xae8 - gp6;
      }
      else {
          ak = ak - hy;
          wa4 -= l;
          gp6 -= xae8;
      }
      l = l + od;
  }

}
