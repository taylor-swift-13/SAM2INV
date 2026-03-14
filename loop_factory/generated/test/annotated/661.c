int main1(int i){
  int lj, zo, k, yr;
  lj=i+13;
  zo=0;
  k=lj;
  yr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == lj;
  loop invariant ((yr == 0) || (yr == k));
  loop invariant ((zo == 0) || (zo == lj));
  loop invariant lj == \at(i, Pre) + 13;
  loop invariant ((yr == 0 && zo == 0) || (yr == k && zo == lj));
  loop assigns yr, zo;
*/
while (1) {
      if (!(zo<lj)) {
          break;
      }
      yr = yr + k;
      zo = lj;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((yr == 0) || (yr == k));
  loop invariant lj <= yr;
  loop assigns zo, lj;
*/
while (lj<=yr-1) {
      zo = zo + k;
      lj = yr;
  }
}