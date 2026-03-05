int main1(int k){
  int mhc, i7, sy;
  mhc=k-2;
  i7=0;
  sy=mhc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i7 == 0;
  loop invariant mhc == \at(k, Pre) - 2;
  loop invariant k == \at(k, Pre) + mhc * (sy - mhc);
  loop invariant sy >= mhc;
  loop invariant k - \at(k, Pre) == mhc * (sy - (\at(k, Pre) - 2));
  loop assigns sy, k;
*/
while (i7+5<=mhc) {
      sy += 1;
      k += mhc;
  }
}