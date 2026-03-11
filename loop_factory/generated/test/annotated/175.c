int main1(int h){
  int d, u9p, mz, el2k, yy33, gil;
  d=h;
  u9p=0;
  mz=45;
  el2k=0;
  yy33=1;
  gil=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mz + el2k == 45;
  loop invariant yy33 == 1 + u9p;
  loop invariant 0 <= el2k;
  loop invariant el2k <= 45;
  loop invariant 0 <= gil;
  loop invariant gil <= 45;
  loop invariant 0 <= u9p;
  loop invariant gil <= yy33;
  loop invariant d == \at(h, Pre);
  loop invariant el2k >= u9p;
  loop invariant (d <= 0) || (u9p <= d);
  loop assigns u9p, mz, el2k, gil, yy33;
*/
for (; mz>0&&u9p<d; u9p++) {
      if (mz<=yy33) {
          gil = mz;
      }
      else {
          gil = yy33;
      }
      yy33 += 1;
      mz -= gil;
      el2k += gil;
  }
}