int main1(){
  int xfu, ss, a9z, wlmx;
  xfu=11;
  ss=xfu;
  a9z=2;
  wlmx=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ss <= xfu;
  loop invariant (wlmx == 1) || (wlmx == -1);
  loop invariant xfu == 11;
  loop invariant 2 <= a9z <= 7;
  loop invariant a9z <= 7;
  loop invariant (a9z - ss) <= -9;
  loop invariant (a9z <= 2) ==> (wlmx == 1);
  loop invariant (ss >= 11);
  loop assigns a9z, ss, wlmx;
*/
while (ss<xfu) {
      if (!(a9z<7)) {
          wlmx = -1;
      }
      if (a9z<=2) {
          wlmx = 1;
      }
      a9z += wlmx;
      ss += 1;
  }
}