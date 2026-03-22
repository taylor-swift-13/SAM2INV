int main1(int t){
  int e12, gs, cu, n5;
  e12=t;
  gs=(t%20)+5;
  cu=(t%20)+5;
  n5=(t%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gs == cu;
  loop invariant cu == n5;
  loop invariant gs <= ((\at(t, Pre) % 20) + 5);
  loop invariant e12 == \at(t, Pre);
  loop invariant t == \at(t, Pre) * (1 + ((\at(t, Pre) % 20) + 5) - gs);
  loop assigns t, gs, cu, n5;
*/
while (gs>0) {
      if (cu>0) {
          if (n5>0) {
              gs = gs - 1;
              cu--;
              n5 -= 1;
          }
      }
      t += e12;
  }
}