int main1(){
  int hkru, k8, q, l7hy;
  hkru=1-7;
  k8=0;
  q=0;
  l7hy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == l7hy;
  loop invariant l7hy >= 0;
  loop assigns l7hy, q;
*/
while (l7hy<hkru) {
      l7hy++;
      q += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 0;
  loop assigns q;
*/
while (q+1<=k8) {
      q += 1;
  }
}