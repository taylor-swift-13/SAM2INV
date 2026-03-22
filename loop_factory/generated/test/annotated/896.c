int main1(){
  int i, az, q;
  i=38;
  az=0;
  q=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant az == i*i + i - (q*q + q);
  loop invariant 0 <= q <= i;
  loop assigns az, q;
*/
while (1) {
      if (!(az<i&&q>0)) {
          break;
      }
      q = q - 1;
      az = az + 1;
      az = az+q+q;
      az = az + 1;
  }
}