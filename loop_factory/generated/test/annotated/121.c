int main1(int t){
  int gu, wji, y1, s7;
  gu=54;
  wji=3;
  y1=2;
  s7=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3 <= wji;
  loop invariant wji <= gu;
  loop invariant 2 <= y1 && y1 <= 11 && (s7 == 1 || s7 == -1);
  loop invariant t == \at(t, Pre) + (wji*(wji+1))/2 - 6;
  loop assigns s7, y1, wji, t;
*/
while (wji<gu) {
      if (y1>=11) {
          s7 = -1;
      }
      if (y1<=2) {
          s7 = 1;
      }
      y1 += s7;
      wji = wji + 1;
      t += wji;
  }
}