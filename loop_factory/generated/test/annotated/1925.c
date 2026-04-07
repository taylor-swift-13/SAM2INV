int main1(){
  int b2, bx, ja, d80, xma2, w, h, b, rd;
  b2=189;
  bx=0;
  ja=6;
  d80=0;
  xma2=3;
  w=bx;
  h=b2;
  b=b2;
  rd=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == b2 + bx;
  loop invariant xma2 == 3 * bx + 3;
  loop invariant ja + d80 == 6;
  loop invariant rd == 4 + (bx + 1) / 2;
  loop invariant b >= b2;
  loop invariant w >= 0;
  loop invariant (0 <= bx && bx <= b2);
  loop invariant (0 <= ja && 0 <= d80 && ja <= 6 && d80 <= 6);
  loop invariant d80 <= bx;
  loop assigns ja, d80, b, h, bx, w, rd, xma2;
*/
while (1) {
      if (!(bx<b2)) {
          break;
      }
      if (!(!(bx%2==0))) {
          if (ja>0) {
              ja = ja - 1;
              d80 = d80 + 1;
          }
      }
      else {
          if (d80>0) {
              d80--;
              ja += 1;
          }
      }
      b = b + ja;
      h += 1;
      bx += 1;
      w += d80;
      rd = rd+(bx%2);
      xma2 = xma2 + 3;
      w += xma2;
  }
}