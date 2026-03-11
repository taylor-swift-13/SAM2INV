int main1(){
  int qsi, rb7p, l0, u6;
  qsi=10;
  rb7p=0;
  l0=4;
  u6=qsi;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rb7p;
  loop invariant rb7p <= qsi;
  loop invariant l0 >= 4;
  loop invariant qsi == 10;
  loop invariant (rb7p == 0) || (rb7p == qsi);
  loop assigns l0, rb7p;
*/
while (1) {
      if (!(rb7p<qsi)) {
          break;
      }
      if (rb7p<qsi/2) {
          l0 = l0 + u6;
      }
      else {
          l0 = l0 + 1;
      }
      rb7p = qsi;
  }
}