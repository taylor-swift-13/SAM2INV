int main1(int w){
  int p6, oyr, ky2, r6;
  p6=38;
  oyr=0;
  ky2=w;
  r6=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= oyr;
  loop invariant oyr <= p6;
  loop invariant r6 == 6 + p6 * oyr;
  loop invariant ky2 == w - oyr;
  loop invariant p6 == 38;
  loop invariant w == \at(w, Pre);
  loop assigns oyr, r6, ky2;
*/
while (1) {
      if (!(oyr < p6)) {
          break;
      }
      oyr++;
      r6 += p6;
      ky2 = w - oyr;
  }
}