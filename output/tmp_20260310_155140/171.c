int main1(int b,int k){
  int n, j, s, w;

  n=(k%25)+11;
  j=n;
  s=n;
  w=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (\at(k, Pre) % 25) + 11;
  loop invariant s <= n;
  loop invariant (s == n) ==> (w == n);

  loop invariant n == (k%25) + 11;
  loop invariant w >= s;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant w >= n;
  loop invariant s >= \at(k, Pre) % 25 + 11;
  loop invariant w >= \at(k, Pre) % 25 + 11;
  loop assigns s, w;
*/
while (s<n) {
      if (s<n) {
          s = s+1;
      }
      w = w+w;
      w = w+s;
  }

}
