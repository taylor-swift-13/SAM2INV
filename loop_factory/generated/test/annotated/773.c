int main1(int l){
  int b6, iy;
  b6=26;
  iy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= iy <= b6;
  loop invariant b6 == 26;
  loop invariant l == \at(l, Pre);
  loop assigns iy;
*/
while (1) {
      if (!(iy+1<=b6)) {
          break;
      }
      iy++;
  }
}