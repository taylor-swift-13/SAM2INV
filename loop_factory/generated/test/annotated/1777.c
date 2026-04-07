int main1(){
  int s8os, rrf9, vb, yr;
  s8os=1;
  rrf9=0;
  vb=0;
  yr=s8os;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rrf9;
  loop invariant rrf9 <= s8os;
  loop invariant s8os == 1;
  loop invariant vb >= 0;
  loop invariant yr >= s8os;
  loop invariant yr >= vb + 1;
  loop assigns vb, rrf9, yr;
*/
while (rrf9 < s8os) {
      vb = vb + yr * yr;
      rrf9 = rrf9 + 1;
      yr += vb;
  }
}