int main1(){
  int ey, q, t4, fj, jxh;
  ey=1-6;
  q=ey;
  t4=0;
  fj=0;
  jxh=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t4 == fj;
  loop invariant jxh == 5 + ey * fj;
  loop invariant ey == (1 - 6);
  loop invariant q == ey;
  loop invariant 0 <= t4;
  loop assigns t4, fj, jxh;
*/
while (fj<=ey-1) {
      t4 = t4 + 1;
      fj++;
      jxh = jxh+ey-q;
      jxh = jxh + q;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fj >= t4;
  loop invariant t4 >= 0;
  loop assigns t4, fj;
*/
while (1) {
      if (!(t4<q)) {
          break;
      }
      t4 = t4 + 1;
      fj++;
      fj = fj*2;
  }
}