int main1(int b,int m){
  int l, s, k;

  l=35;
  s=0;
  k=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (s<l) {
      k = k-k;
      k = k+(-3);
      s = s+1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */

while (s>=3) {
      s = s-3;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */

while (s<=k-1) {
      s = s+1;
  }
/*@
  assert !(s<=k-1) &&
         (l == 35);
*/

}
