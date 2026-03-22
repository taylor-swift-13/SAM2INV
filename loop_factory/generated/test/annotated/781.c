int main1(int i){
  int yw, zq1v, r7s, en;
  yw=56;
  zq1v=0;
  r7s=-4;
  en=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r7s == -4 + en * zq1v;
  loop invariant zq1v <= yw;
  loop invariant zq1v >= 0;
  loop invariant yw == 56;
  loop invariant r7s + zq1v == -4;
  loop invariant i == \at(i, Pre);
  loop assigns r7s, zq1v;
*/
while (1) {
      if (!(zq1v+1<=yw)) {
          break;
      }
      r7s = r7s + en;
      zq1v = zq1v + 1;
  }
}