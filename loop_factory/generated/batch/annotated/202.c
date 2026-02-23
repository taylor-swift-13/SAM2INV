int main1(int b,int k){
  int n, j, s, w;

  n=(k%25)+11;
  j=n;
  s=n;
  w=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (\at(k, Pre) % 25) + 11;
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);

  loop invariant s == n || s >= n*(n+1);
  loop invariant n == \at(k, Pre) % 25 + 11;
  loop invariant s <= n;
  loop invariant s >= \at(k, Pre) % 25 + 11;
  loop invariant b == \at(b, Pre) &&
                   k == \at(k, Pre) &&
                   n == (\at(k, Pre) % 25) + 11 &&
                   s <= n;
  loop invariant n == (k % 25) + 11;

  loop assigns s;
*/
while (s<n) {
      if (s<n) {
          s = s+1;
      }
      s = s*s+s;
  }

}
