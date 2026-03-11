int main1(int a,int b){
  int m, n, l, v;

  m=(b%40)+13;
  n=0;
  l=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant v >= 0;
  loop invariant v % 8 == 0;
  loop invariant m == (\at(b, Pre) % 40) + 13;

  loop invariant (l < m/2) ==> v == 0;
  loop invariant v % 2 == 0;
  loop invariant l >= 0;
  loop invariant (l <= m/2) ==> v == 0;

  loop invariant v % 2 == 0 && v >= 0;
  loop invariant (m >= 0) ==> l <= m;
  loop invariant m == (b % 40) + 13;
  loop invariant -26 <= m && m <= 52;
  loop invariant v % 4 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == (b%40) + 13;


  loop assigns l, v;
*/
while (l<m) {
      if (l>=m/2) {
          v = v+4;
      }
      l = l+1;
      v = v+v;
  }
/*@
  assert (m == (\at(b, Pre) % 40) + 13) &&
         (l == m) &&
         (v >= 0) &&
         (v % 2 == 0);
*/

}
