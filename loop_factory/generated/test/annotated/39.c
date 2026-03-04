int main1(int j,int e){
  int dlb1, tz, u4o4;
  dlb1=(e%6)+19;
  tz=0;
  u4o4=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == 2*u4o4 - \at(e, Pre);
  loop invariant dlb1 == (\at(e, Pre) % 6) + 19;
  loop invariant j == \at(j, Pre) + (u4o4 - \at(e, Pre)) * \at(e, Pre) + (u4o4 - \at(e, Pre)) * ((u4o4 - \at(e, Pre)) + 1);
  loop invariant j == \at(j, Pre) + (u4o4 - \at(e, Pre)) * (u4o4 + 1);
  loop invariant u4o4 >= \at(e, Pre);
  loop invariant 2*u4o4 - e == \at(e, Pre);
  loop invariant tz == 0;
  loop invariant e >= \at(e, Pre);
  loop invariant u4o4 <= e;
  loop invariant dlb1 >= 0;
  loop invariant (u4o4 - \at(e, Pre)) >= 0;
  loop assigns u4o4, j, e;
*/
while (1) {
      if (!(u4o4<dlb1)) {
          break;
      }
      if (u4o4<dlb1) {
          u4o4 += 1;
      }
      j += tz;
      e += 2;
      j = j + e;
  }
}