int main1(){
  int hx, q, ahv, dslz;
  hx=1+10;
  q=0;
  ahv=3;
  dslz=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ahv == 3 + 5*q;
  loop invariant dslz == 3*q + (5*q*(q+1))/2;
  loop invariant 0 <= q <= hx;
  loop assigns ahv, dslz, q;
*/
while (1) {
      if (!(q<hx)) {
          break;
      }
      ahv = ahv + 5;
      dslz = dslz + ahv;
      q += 1;
  }
}