int main1(int j,int y){
  int r, jlsk, xzt, vv2;
  r=80;
  jlsk=3;
  xzt=0;
  vv2=9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xzt == (jlsk - 3) % 2;
  loop invariant vv2 == 9 - 2 * ((jlsk - 3) % 2);
  loop invariant 3 <= jlsk <= r;
  loop invariant j == \at(j, Pre) + (jlsk - 2)/2;
  loop invariant y == \at(y, Pre);
  loop assigns j, jlsk, vv2, xzt;
*/
while (jlsk<r) {
      if (xzt==0) {
          xzt += 2;
          vv2 -= 2;
          xzt = 1;
      }
      else {
          xzt -= 2;
          vv2 += 2;
          xzt = 0;
      }
      jlsk++;
      j += xzt;
  }
}