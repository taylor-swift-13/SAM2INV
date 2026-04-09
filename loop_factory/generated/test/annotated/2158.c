int main1(int h){
  int q, w1r7, b1, wl;
  q=h;
  w1r7=0;
  b1=0;
  wl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b1 == w1r7;
  loop invariant wl == w1r7;
  loop invariant w1r7 >= 0;
  loop invariant 4 * (h - \at(h, Pre)) == w1r7 * (w1r7 + 2);
  loop invariant q == \at(h,Pre);
  loop invariant (q < 0) || (w1r7 <= q + 1);
  loop assigns wl, b1, w1r7, h;
*/
while (w1r7<q) {
      wl += 2;
      b1 += 2;
      w1r7 += 2;
      h = h + w1r7;
  }
}