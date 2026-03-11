int main1(int a,int p){
  int n, b, s, v;

  n=(p%40)+5;
  b=0;
  s=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= s;

  loop invariant (s < n/2) ==> (v == 3*s);
  loop invariant n == (\at(p, Pre) % 40) + 5;

  loop invariant v % 3 == 0;

  loop invariant n == \at(p, Pre) % 40 + 5;

  loop invariant n == ((\at(p, Pre)) % 40) + 5;
  loop invariant (s <= n/2) ==> (v == 3*s);
  loop invariant n == ((\at(p,Pre) % 40) + 5);
  loop invariant p == \at(p,Pre) && a == \at(a,Pre);
  loop invariant s <= n/2 ==> v == 3*s;

  loop invariant n == (p % 40) + 5;
  loop invariant s >= 0;
  loop invariant (s <= n/2) ==> v == 3*s;
  loop invariant -3*s <= v && v <= 3*s && v % 3 == 0;

  loop assigns s, v;
*/
while (s<n) {
      if (s<n/2) {
          v = v+3;
      }
      else {
          v = v-3;
      }
      s = s+1;
  }
/*@
  assert (n == (\at(p, Pre) % 40) + 5) &&
         (s >= n) &&
         (s >= 0) &&
         (v % 3 == 0);
*/

}
