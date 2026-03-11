int main1(int m,int n){
  int s, w, v, l;

  s=64;
  w=0;
  v=0;
  l=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 64;
  loop invariant 0 <= v && v <= s;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant v <= s/2 ==> l == n;
  loop invariant v >= s/2 ==> l >= n;
  loop assigns l, v;
*/
while (v<s) {
      if (v>=s/2) {
          l = l+2;
      }
      v = v+1;
  }
/*@
  assert (s == 64) &&
         (v == s) &&
         (l >= n);
*/

}
