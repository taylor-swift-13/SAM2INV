int main1(){
  int lwb, qn, az, qm, d;
  lwb=73;
  qn=lwb;
  az=0;
  qm=0;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (qn == lwb + d);
  loop invariant (qm == d % 11);
  loop invariant (az == d / 11);
  loop invariant 0 <= d;
  loop invariant 0 <= qm;
  loop invariant qm <= 10;
  loop invariant d == 11*az + qm;
  loop invariant az >= 0;
  loop assigns d, qm, az, qn;
*/
while (1) {
      if (!(qn<lwb)) {
          break;
      }
      d++;
      qm = qm + 1;
      if (qm>=11) {
          qm -= 11;
          az = az + 1;
      }
      qn++;
  }
}