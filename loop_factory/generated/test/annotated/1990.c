int main1(int q){
  int gpi, ls, g, vl;
  gpi=q;
  ls=0;
  g=5;
  vl=q*2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vl - g == (2 * \at(q, Pre) - 5);
  loop invariant gpi == \at(q, Pre);
  loop invariant (gpi >= 0 ==> ls <= gpi);
  loop invariant ls >= 0;
  loop invariant q >= \at(q,Pre);
  loop assigns g, ls, vl, q;
*/
while (ls < gpi) {
      g = g + q;
      ls++;
      vl = vl + q;
      q = q + ls;
  }
}