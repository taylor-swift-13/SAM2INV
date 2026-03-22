int main1(int o){
  int zjc, x, u, qtla, m2x;
  zjc=35;
  x=0;
  u=0;
  qtla=0;
  m2x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m2x == zjc * u;
  loop invariant qtla == 0;
  loop invariant m2x == u * (zjc - x);
  loop invariant 0 <= u;
  loop invariant u <= zjc;
  loop invariant qtla <= zjc;
  loop assigns m2x, u, qtla;
*/
while (u<zjc) {
      if (m2x<zjc) {
          qtla = u;
      }
      m2x = m2x+zjc-x;
      u = u + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qtla <= zjc;
  loop invariant m2x >= 0;
  loop invariant u == zjc;
  loop assigns m2x, o, qtla;
*/
while (qtla<zjc) {
      m2x = m2x + u;
      o = o+zjc-qtla;
      qtla = zjc;
  }
}