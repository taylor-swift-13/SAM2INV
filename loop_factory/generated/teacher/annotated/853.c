int main1(int b,int k){
  int n, u, e, v;

  n=b+11;
  u=1;
  e=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == b + 11;

  loop invariant (e < n/2) ==> v == n;


  loop invariant v >= n;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= e;
  loop invariant (e <= n/2) ==> v == n;

  loop invariant (e < n/2) ==> (v == n);


  loop invariant v >= n && ((v - n) % 2 == 0);

  loop invariant b == \at(b, Pre) &&
                    k == \at(k, Pre) &&
                    0 <= e && (n < 0 || e <= n);

  loop invariant n == \at(b,Pre) + 11;
  loop invariant (v - n) % 2 == 0;

  loop invariant (e <= n/2) ==> (v == n);

  loop assigns e, v;
*/
while (e<n) {
      if (e>=n/2) {
          v = v+2;
      }
      e = e+1;
  }

}
