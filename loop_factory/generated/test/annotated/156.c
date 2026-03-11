int main1(int z){
  int u8, upw, at7;
  u8=(z%7)+11;
  upw=2;
  at7=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant at7 == z * (upw - 1);
  loop invariant at7 == \at(z, Pre) + (upw - 2) * z;
  loop invariant 2 <= upw;
  loop invariant u8 == ((z % 7) + 11);
  loop invariant upw <= u8;
  loop assigns at7, upw;
*/
while (1) {
      at7 += z;
      upw = upw + 1;
      if (upw>=u8) {
          break;
      }
  }
}