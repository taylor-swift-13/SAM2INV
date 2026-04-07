int main1(int f){
  int grzc, gyc, h0, we, la;
  grzc=52;
  gyc=0;
  h0=gyc;
  we=gyc;
  la=grzc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= gyc && gyc <= grzc);
  loop invariant (we == (-gyc + 2*(gyc/3)));
  loop invariant la == grzc * (gyc + 1);
  loop invariant h0 == - (gyc % 2);
  loop invariant grzc == 52;
  loop assigns gyc, h0, la, we;
*/
while (1) {
      if (!(gyc < grzc)) {
          break;
      }
      gyc += 1;
      h0 = h0 + 2*(gyc % 2 == 0) - 1;
      la += grzc;
      we = (we + 2*(gyc % 3 == 0))+(-(1));
  }
}