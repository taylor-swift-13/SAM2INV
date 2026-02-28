int main1(int b,int n){
  int e, s, v, g;

  e=62;
  s=0;
  v=n;
  g=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant 3*(n - v) == 5*s;
  loop invariant s >= 0;
  loop invariant s % 3 == 0;
  loop invariant v <= n;
  loop invariant (3*v + 5*s == 3*n);
  loop invariant (s % 3 == 0);
  loop invariant (0 <= s);
  loop invariant (s <= e + 2);
  loop invariant (v <= n);
  loop invariant 0 <= s;
  loop invariant 3*v + 5*s == 3*n;
  loop invariant b == \at(b, Pre);
  loop invariant v == n - 5 * (s / 3);
  loop invariant s <= e + 1;

  loop invariant (n == \at(n, Pre));
  loop assigns v, s;
*/
while (s<e) {
      v = v+g+g;
      v = v+1;
      s = s+3;
  }

}
