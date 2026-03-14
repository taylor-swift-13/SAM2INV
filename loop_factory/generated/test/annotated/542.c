int main1(int d){
  int ctof, d47, rj, z, aky, om;
  ctof=d;
  d47=0;
  rj=0;
  z=0;
  aky=8;
  om=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ctof == d;
  loop invariant rj >= 0;
  loop invariant aky == 8 - rj;
  loop invariant z == rj * (17 - rj) / 2;
  loop invariant om == -6 + d47 * rj;
  loop invariant 0 <= aky;
  loop assigns rj, z, aky, om;
*/
while (1) {
      if (!(rj<ctof&&aky>0)) {
          break;
      }
      rj++;
      z = z + aky;
      aky -= 1;
      om = om + d47;
  }
}