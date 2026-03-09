int main1(int l){
  int ywp, gb, l5, tv;
  ywp=l+14;
  gb=0;
  l5=0;
  tv=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tv;
  loop invariant tv <= 6;
  loop invariant gb + tv == 6;
  loop invariant l + l5 == \at(l, Pre) + 12*gb - gb*gb;
  loop invariant ywp == \at(l, Pre) + 14;
  loop invariant l == \at(l, Pre) + gb*(11 - gb)/2;
  loop invariant l5 == (6 - tv) * (tv + 7) / 2;
  loop assigns gb, l, l5, tv;
*/
while (gb<ywp&&tv>0) {
      gb = gb + 1;
      l5 += tv;
      tv--;
      l += tv;
  }
}