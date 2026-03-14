int main1(){
  int ft9, jmr, zx, a, yz;
  ft9=1;
  jmr=0;
  zx=0;
  a=-4;
  yz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yz == zx*(zx - 1)/2;
  loop invariant 0 <= zx <= ft9;
  loop invariant a <= zx;
  loop invariant (zx > 0) ==> (a == zx - 1);
  loop assigns a, yz, zx;
*/
while (zx<=ft9-1) {
      a = zx;
      yz = yz + a;
      zx += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yz == jmr;
  loop invariant a == jmr*(jmr+1)/2;
  loop invariant zx == 1;
  loop invariant jmr <= zx;
  loop assigns yz, jmr, a;
*/
while (1) {
      if (!(jmr<zx)) {
          break;
      }
      yz = yz + 1;
      jmr += 1;
      a = a + yz;
  }
}