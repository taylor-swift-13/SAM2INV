int main1(int b){
  int ew, om, y, wrx;
  ew=38;
  om=-4;
  y=0;
  wrx=om;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre) + om*y;
  loop invariant 0 <= y <= ew;
  loop invariant (wrx <= ew - y);
  loop assigns b, y, wrx;
*/
while (y<ew) {
      y++;
      b += om;
      wrx = ew-y;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 1;
  loop invariant (y <= ew);
  loop assigns y;
*/
while (1) {
      if (!(y<=om-1)) {
          break;
      }
      y++;
  }
}