int main1(int e){
  int u8, sg5, ln5, dr;
  u8=31;
  sg5=0;
  ln5=e;
  dr=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= sg5;
  loop invariant sg5 <= u8;
  loop invariant (ln5 + sg5) == \at(e, Pre);
  loop invariant dr == \at(e, Pre) + sg5;
  loop invariant e + ((sg5*(sg5+1))/2) == ((sg5+1) * \at(e, Pre));
  loop invariant u8 == 31;
  loop assigns ln5, sg5, dr, e;
*/
while (sg5 < u8) {
      ln5 -= 1;
      sg5++;
      dr++;
      e = e + ln5;
  }
}