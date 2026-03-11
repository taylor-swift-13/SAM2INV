int main1(int f){
  int i4x, w4, ss, ekl, ov7;
  i4x=168;
  w4=i4x;
  ss=0;
  ekl=0;
  ov7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ss == f * ekl;
  loop invariant 0 <= ekl <= i4x;
  loop assigns ss, ekl;
*/
while (ekl<i4x) {
      ss += f;
      ekl++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ov7 == w4 * (i4x - 168) * (i4x + 167) / 2;
  loop invariant i4x >= 168;
  loop invariant w4 == 168;
  loop assigns ov7, i4x;
*/
while (1) {
      if (!(i4x-1>=0)) {
          break;
      }
      ov7 = ov7+w4*i4x;
      i4x++;
  }
}