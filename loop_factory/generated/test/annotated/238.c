int main1(int r){
  int w7, cv, v, hs;
  w7=69;
  cv=0;
  v=0;
  hs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= hs <= w7;
  loop invariant v == hs * \at(r, Pre) + w7 * hs * (hs - 1) / 2;
  loop invariant w7 == 69;
  loop invariant r - hs * w7 == \at(r, Pre);
  loop assigns hs, v, r;
*/
while (hs<w7) {
      hs = hs + 1;
      v += r;
      r += w7;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cv == 0;
  loop invariant w7 == 69;
  loop assigns v;
*/
for (; v+1<=cv; v++) {
  }
}