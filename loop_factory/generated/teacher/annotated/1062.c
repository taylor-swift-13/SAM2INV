int main1(int a,int m){
  int l, u, v, q;

  l=(a%39)+13;
  u=2;
  v=u;
  q=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 17*u - 32 && q == 8 && u >= 2;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant v - (2*q + 1) * u == -4*q;
  loop invariant q == 8;
  loop invariant l == (a % 39) + 13;
  loop invariant u >= 2;
  loop invariant v >= 2;
  loop invariant l == (\at(a, Pre) % 39) + 13;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v == (2*q + 1) * u - 4 * q;
  loop invariant v == (2*q+1)*u - 32;
  loop invariant v == u*(2*q + 1) - 4*q;
  loop invariant u >= 2 && v >= 2 && q == 8 && l == (\at(a, Pre) % 39) + 13 && a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant u >= 2 && a == \at(a,Pre) && m == \at(m,Pre);
  loop invariant v - (2*q+1)*u == -4*q;
  loop invariant q == 8 && u >= 2 && l == (\at(a, Pre) % 39) + 13 && a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant v == (2*q+1)*u - 4*q;
  loop assigns u, v;
*/
while (1) {
      v = v+q+q;
      v = v+1;
      u = u+1;
  }

}
