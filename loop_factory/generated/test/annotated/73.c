int main1(int k){
  int r9, z846;
  r9=k-7;
  z846=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r9 == \at(k, Pre) - 7;
  loop invariant k == \at(k, Pre) + z846 * r9;
  loop invariant 0 <= z846;
  loop invariant z846 <= r9 || z846 == 0;
  loop assigns k, z846;
*/
while (z846<r9) {
      z846 += 1;
      if (z846<=z846) {
          z846 = z846;
      }
      k = k + r9;
  }
}