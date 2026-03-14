int main1(int y,int u){
  int q, u0, bfa, g7, pa;
  q=y+16;
  u0=0;
  bfa=0;
  g7=0;
  pa=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pa == u0;
  loop invariant g7 == u0 % 4;
  loop invariant bfa == u0 / 4;
  loop invariant 0 <= u0;
  loop invariant 0 <= g7;
  loop invariant g7 <= 3;
  loop invariant 0 <= bfa;
  loop invariant q == \at(y, Pre) + 16;
  loop invariant q == y + 16;
  loop assigns u0, g7, pa, bfa;
*/
for (; u0<q; u0 = u0 + 1) {
      g7 += 1;
      pa += 1;
      if (g7>=4) {
          g7 -= 4;
          bfa = bfa + 1;
      }
  }
}