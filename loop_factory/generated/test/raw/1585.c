int main1(){
  int xni, g, r4, cz, ph, kw8, qm, iz, z3, jb;

  xni=1;
  g=1;
  r4=0;
  cz=25;
  ph=xni;
  kw8=xni;
  qm=0;
  iz=g;
  z3=0;
  jb=g;

  while (r4<xni) {
      r4++;
      if (ph<=cz) {
          cz = ph;
      }
      if (z3<ph+4) {
          ph = ph + 1;
      }
      z3 = z3+r4-cz;
      jb = jb+r4-cz;
      kw8 += r4;
      iz = ph+kw8+qm;
      ph = ph + 1;
      if ((g%9)==0) {
          jb = jb + 1;
      }
      ph += qm;
      iz = iz + 5;
  }

}
