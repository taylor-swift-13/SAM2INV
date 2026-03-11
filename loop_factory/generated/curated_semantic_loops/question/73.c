int main1(int b,int k){
  int n, j, s, w;

  n=(k%25)+11;
  j=n;
  s=n;
  w=j;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (s<n) {
      if (s<n) {
          s = s+1;
      }
      s = s*s+s;
  }
/*@
  assert !(s<n) &&
         (n == (\at(k, Pre) % 25) + 11);
*/

}
