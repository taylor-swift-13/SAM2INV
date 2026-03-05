int main1(int t){
  int gh, x41, ma2;
  gh=t*3;
  x41=gh;
  ma2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x41 <= gh;
  loop invariant t == \at(t, Pre);
  loop invariant gh == 3 * t;
  loop invariant 0 <= ma2 <= 6;
  loop assigns ma2, x41;
*/
while (x41<gh) {
      ma2++;
      if (ma2>=7) {
          ma2 = ma2 - 7;
          ma2++;
      }
      x41 += 1;
  }
}