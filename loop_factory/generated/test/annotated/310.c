int main1(int i,int m){
  int qq, m4l9, ce, p3y;
  qq=m-9;
  m4l9=qq;
  ce=-8;
  p3y=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m4l9 <= qq;
  loop invariant ((qq - m4l9) % 6) == 0;
  loop invariant m4l9 <= (\at(m, Pre) - 9);
  loop invariant (m4l9 % 6) == (((\at(m, Pre) - 9) % 6));
  loop invariant qq == (m - 9);
  loop assigns m4l9;
*/
while (1) {
      if (!(m4l9-6>=0)) {
          break;
      }
      m4l9 -= 6;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p3y >= m;
  loop invariant i + 8*p3y == \at(i, Pre) + 8 * m;
  loop assigns m4l9, i, p3y;
*/
while (1) {
      if (!(p3y<ce)) {
          break;
      }
      m4l9 = ce-p3y;
      i += ce;
      p3y += 1;
  }
}