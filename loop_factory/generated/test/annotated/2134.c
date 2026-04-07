int main1(int b){
  int pvt, y, w;
  pvt=b;
  y=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pvt == \at(b, Pre);
  loop invariant (pvt <= 0) ==> (y == 0 && w == 0 && b == \at(b, Pre));
  loop invariant b == \at(b, Pre) + pvt * y;
  loop invariant y >= 0;
  loop invariant (pvt >= 0 ==> y <= pvt);
  loop invariant (-3 * y) <= w;
  loop invariant w <= (3 * y);
  loop invariant (w % 3) == 0;
  loop assigns b, w, y;
*/
while (1) {
      if (!(y<pvt)) {
          break;
      }
      if (!(!(y<pvt/2))) {
          w = w - 3;
      }
      else {
          w = w + 3;
      }
      y++;
      b += pvt;
  }
}