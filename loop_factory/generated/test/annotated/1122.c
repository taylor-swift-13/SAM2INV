int main1(int c,int d){
  int ir, k5hc, a, bs, n3;
  ir=c*4;
  k5hc=0;
  a=0;
  bs=0;
  n3=k5hc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= bs;
  loop invariant ir == 4 * \at(c,Pre);
  loop invariant c >= \at(c,Pre);
  loop invariant a - bs * \at(c, Pre) >= 0;
  loop assigns bs, a, c;
*/
while (bs<ir) {
      bs = bs + 1;
      a = a + c;
      c = c+(bs%8);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns n3, ir, c;
*/
while (ir<a) {
      n3 = n3 + c;
      ir = ir + 1;
      c = c + n3;
  }
}