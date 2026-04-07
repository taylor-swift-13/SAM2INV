int main1(int m){
  int d, jn, nu, ar, dd;
  d=m;
  jn=0;
  nu=0;
  ar=0;
  dd=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dd == 2 * jn + 1;
  loop invariant ar == jn * jn;
  loop invariant d == \at(m, Pre);
  loop invariant (jn >= 0) && (0 <= nu && nu <= 2 * jn) && ((d >= 0) ==> (jn <= d));
  loop assigns ar, dd, jn, nu;
*/
while (jn < d) {
      ar += dd;
      dd += 2;
      jn = jn + 1;
      nu = nu+(dd%3);
  }
}