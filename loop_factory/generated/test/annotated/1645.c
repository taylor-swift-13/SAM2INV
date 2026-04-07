int main1(int l){
  int yp, cy, n2;
  yp=(l%30)+11;
  cy=0;
  n2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n2 == 16 * cy;
  loop invariant l == \at(l, Pre) + 8 * cy * (cy + 1);
  loop invariant yp == ((\at(l, Pre) % 30) + 11);
  loop assigns cy, n2, l;
*/
while (cy<yp) {
      cy++;
      n2 = n2 + 16;
      l += n2;
  }
}