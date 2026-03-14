int main1(){
  int v, n, oe, f, bn;
  v=1+25;
  n=0;
  oe=1;
  f=0;
  bn=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == (oe - 1) * oe * (2 * oe - 1) / 6;
  loop invariant bn == 26;
  loop invariant v == 26;
  loop invariant bn == 26 + (oe - 1) * n;
  loop invariant 1 <= oe <= v + 1;
  loop invariant n == 0;
  loop assigns f, oe, bn;
*/
while (oe<=v) {
      f = f+oe*oe;
      oe += 1;
      bn += n;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oe >= 2;
  loop invariant v <= f;
  loop assigns oe, v;
*/
for (; v<=f-1; v++) {
      oe = oe+(-4);
      oe += 6;
  }
}