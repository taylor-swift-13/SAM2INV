int main1(int n){
  int l, ft, ne;
  l=n*3;
  ft=0;
  ne=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ft >= 0;
  loop invariant ne == -8 + 3 * ft;
  loop invariant l == 3 * \at(n, Pre);
  loop invariant (l < 0) || (ft <= l);
  loop invariant l == 3 * n;
  loop assigns ft, ne;
*/
while (1) {
      ne = ne + 3;
      ft += 1;
      if (ft>=l) {
          break;
      }
  }
}