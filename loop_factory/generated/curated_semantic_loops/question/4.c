int main1(int w,int g){
  int ew, omy4, y, g0z, svlb, o;
  ew=g*3;
  omy4=0;
  y=0;
  g0z=0;
  svlb=0;
  o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (omy4<ew) {
      if (!(!(omy4%8==0))) {
          if (omy4%9==0) {
              svlb++;
          }
          else {
              if (omy4%5==0) {
                  g0z = g0z + 1;
              }
              else {
                  y++;
              }
          }
      }
      else {
          o = o + 1;
      }
      omy4 = omy4 + 1;
      w = w + omy4;
  }
/*@
  assert !(omy4<ew) &&
         (w == \at(w,Pre) + (omy4 * (omy4 + 1)) / 2);
*/

}