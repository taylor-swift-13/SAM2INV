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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= r4;
  loop invariant r4 <= xni;
  loop invariant kw8 == 1 + (r4*(r4 + 1))/2;
  loop invariant ph >= 1 + r4;
  loop invariant jb - z3 == 1;
  loop invariant g == 1;
  loop invariant (r4 == 0 ==> iz == 1) && (r4 > 0 ==> iz == ph + kw8 + 4);
  loop invariant xni == 1;
  loop invariant qm == 0;
  loop invariant iz == ph + kw8 + qm + 5*r4 - 1;
  loop invariant 1 <= cz;
  loop invariant cz <= 25;
  loop assigns r4, cz, ph, z3, jb, kw8, iz;
*/
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