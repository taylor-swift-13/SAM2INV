int main1(){
  int cu, c1fi, n6d, k5i, ns, znn;
  cu=(1%15)+11;
  c1fi=0;
  n6d=0;
  k5i=0;
  ns=cu;
  znn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k5i == n6d;
  loop invariant ns >= cu;
  loop invariant ns <= (cu + 6 * k5i);
  loop invariant znn == 3 * k5i;
  loop invariant 0 <= k5i <= cu;
  loop assigns k5i, n6d, znn, ns;
*/
while (k5i<=cu-1) {
      k5i++;
      n6d = n6d + 1;
      znn = znn + 3;
      ns = ns+(k5i%7);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c1fi <= znn;
  loop invariant k5i == 12 + c1fi*(c1fi-1)/2;
  loop invariant znn == 36;
  loop assigns cu, k5i, c1fi;
*/
while (1) {
      cu = cu+k5i*c1fi;
      k5i = k5i + c1fi;
      c1fi++;
      if (c1fi>=znn) {
          break;
      }
  }
}