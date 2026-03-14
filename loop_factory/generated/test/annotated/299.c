int main1(){
  int d1, rox, d0, kf;
  d1=(1%33)+12;
  rox=0;
  d0=0;
  kf=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rox;
  loop invariant rox <= d1;
  loop invariant kf == 8 + rox*d1 - rox*(rox+1)/2;
  loop invariant d0 >= 0;
  loop invariant (rox == 0 && d0 == 0) || (rox > 0 && d0 == d1 - rox);
  loop assigns rox, d0, kf;
*/
while (1) {
      if (!(rox<d1)) {
          break;
      }
      rox = rox + 1;
      d0 = (d1)+(-(rox));
      kf += d0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rox == d1 + d0*(d0 - 1)/2;
  loop invariant rox >= 13;
  loop invariant d0 < kf;
  loop invariant rox >= d0;
  loop invariant d0 >= 0;
  loop assigns rox, d0;
*/
while (1) {
      rox += d0;
      d0++;
      if (d0>=kf) {
          break;
      }
  }
}