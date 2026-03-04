int main1(int w,int i,int h){
  int fg, d7, ab8, uo;
  fg=61;
  d7=2;
  ab8=0;
  uo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uo <= fg;
  loop invariant w == \at(w, Pre) + 2 * uo;
  loop invariant h == \at(h, Pre) + d7 * uo;
  loop invariant ab8 == uo % 7;
  loop invariant i == \at(i, Pre);
  loop invariant fg == 61;
  loop invariant 0 <= uo;
  loop invariant 0 <= ab8;
  loop invariant ab8 <= 6;
  loop invariant w - \at(w,Pre) == 2 * uo;
  loop invariant h - \at(h,Pre) == d7 * uo;
  loop invariant 0 <= uo <= fg;
  loop assigns ab8, uo, w, h;
*/
while (1) {
      if (!(uo<fg)) {
          break;
      }
      ab8 = (ab8+1)%7;
      uo = uo + 1;
      w += 2;
      h = h + d7;
  }
}