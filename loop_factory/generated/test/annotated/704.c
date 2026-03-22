int main1(){
  int hmx, m9, e8, wmmz;
  hmx=0;
  m9=0;
  e8=0;
  wmmz=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m9 == e8;
  loop invariant wmmz + m9 == 6;
  loop invariant 0 <= e8 <= 6;
  loop invariant 0 <= wmmz <= 6;
  loop invariant hmx >= m9;
  loop assigns hmx, m9, wmmz, e8;
*/
while (1) {
      if (!(wmmz>0)) {
          break;
      }
      hmx = hmx+1*1;
      m9 = m9+1*1;
      wmmz--;
      e8 = e8+1*1;
      hmx = hmx*hmx+hmx;
  }
}