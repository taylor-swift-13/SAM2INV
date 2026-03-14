int main1(){
  int mhzk, r, m8;
  mhzk=55;
  r=mhzk;
  m8=mhzk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r >= 0;
  loop invariant r <= 55;
  loop invariant mhzk == 55;
  loop invariant m8 == mhzk + (mhzk - r) * mhzk - ((mhzk - r) * (mhzk - r - 1)) / 2;
  loop assigns m8, r;
*/
while (1) {
      if (!(r>=1)) {
          break;
      }
      m8 += r;
      r--;
  }
}