int main1(){
  int n, q4, p, vm5;
  n=(1%16)+16;
  q4=0;
  p=n;
  vm5=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == n + q4 * vm5;
  loop invariant vm5 == n;
  loop invariant 0 <= q4;
  loop invariant q4 <= n;
  loop assigns p, q4;
*/
for (; q4<=n-1; q4 = q4 + 1) {
      p += vm5;
  }
}