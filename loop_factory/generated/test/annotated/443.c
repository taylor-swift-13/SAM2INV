int main1(){
  int bw9, gn, dy, jt, l8;
  bw9=1+7;
  gn=-3;
  dy=0;
  jt=0;
  l8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l8 == gn * dy;
  loop invariant 0 <= dy <= 1;
  loop invariant l8 <= 0;
  loop invariant (dy == 0) ==> (bw9 == 8);
  loop invariant (dy != 0) ==> (bw9 == gn);
  loop invariant gn <= bw9;
  loop assigns dy, l8, bw9;
*/
while (gn+1<=bw9) {
      dy += 1;
      l8 = l8 + gn;
      bw9 = ((gn+1))+(-(1));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dy >= 1;
  loop invariant l8 <= 0;
  loop invariant ((dy % 7) == 1);
  loop invariant (l8 == -3) || (l8 == 0);
  loop invariant jt == 0;
  loop invariant bw9 <= 0;
  loop assigns dy, l8;
*/
while (1) {
      if (!(dy<jt)) {
          break;
      }
      l8 -= l8;
      l8 = dy-dy;
      dy = dy + 7;
  }
}