int main1(int a,int b){
  int u, d, n, e;

  u=b+12;
  d=u;
  n=0;
  e=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == b + 12;
  loop invariant 0 <= n;

  loop invariant e >= a;
  loop invariant (e - a) % 4 == 0;
  loop invariant u == \at(b, Pre) + 12 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant n >= 0 && e >= a;
  loop invariant u == \at(b,Pre) + 12;
  loop invariant n % 3 == 0;
  loop invariant n >= 0;
  loop invariant e >= \at(a,Pre);
  loop invariant (e - \at(a,Pre)) % 4 == 0;
  loop invariant a == \at(a,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n >= 0;
  loop invariant n % 3 == 0 && e >= a && (e - a) % 4 == 0;
  loop invariant (n + 3) % 3 == 0;
  loop invariant ((e - a) % 4) == 0;
  loop invariant (n % 3) == 0;
  loop invariant (n < u/2) ==> e == a;
  loop invariant n >= 0 && n % 3 == 0;
  loop invariant e >= \at(a, Pre) && (e - \at(a, Pre)) % 4 == 0;
  loop invariant n == 0 || n >= 6;
  loop assigns e, n;
*/
while (n<u) {
      if (n>=u/2) {
          e = e+4;
      }
      n = n+1;
      n = n*3+3;
  }
/*@
  assert (u == \at(b, Pre) + 12) &&
         (d == u) &&
         (n >= u) &&
         (n % 3 == 0) &&
         (e >= \at(a, Pre)) &&
         ((e - \at(a, Pre)) % 4 == 0) &&
         ((u <= 0 ==> e == \at(a, Pre)));
*/

}
