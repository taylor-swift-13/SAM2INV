int main1(){
  int g67, m8q3, gd, vu, ij;
  g67=1+14;
  m8q3=0;
  gd=0;
  vu=0;
  ij=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= m8q3;
  loop invariant m8q3 <= g67;
  loop invariant gd == 10 * m8q3;
  loop invariant ij == (m8q3 * (m8q3 + 1)) / 2 + 5 * m8q3;
  loop invariant vu == ij;
  loop assigns m8q3, gd, vu, ij;
*/
while (1) {
      if (!(m8q3 < g67)) {
          break;
      }
      m8q3 = (gd += 5, vu += 5, ij += 5, m8q3 + 1);
      vu = vu + m8q3;
      gd = gd + 5;
      ij = ij + m8q3;
  }
}