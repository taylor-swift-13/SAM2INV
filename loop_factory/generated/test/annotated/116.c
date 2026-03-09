int main1(int q){
  int kj, dr5, mpm, hc;
  kj=q*5;
  dr5=0;
  mpm=2;
  hc=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mpm - hc == -3;
  loop invariant mpm == 2 + 3*dr5;
  loop invariant 0 <= dr5;
  loop invariant kj == q * 5;
  loop assigns dr5, mpm, hc;
*/
for (; dr5<=kj-1; dr5 = dr5 + 1) {
      mpm = mpm + 3;
      hc = hc + 3;
  }
}