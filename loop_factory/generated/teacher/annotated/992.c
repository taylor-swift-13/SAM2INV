int main1(int m,int n){
  int l, a, v, p;

  l=n+7;
  a=0;
  v=n;
  p=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(n, Pre) + 5*a && p == 4*a && a >= 0;
  loop invariant n == \at(n, Pre) && m == \at(m, Pre) && l == \at(n, Pre) + 7;
  loop invariant l == \at(n, Pre) + 7 && n == \at(n, Pre) && m == \at(m, Pre);
  loop invariant p == 4*a;
  loop invariant v == 5*a + \at(n, Pre);
  loop invariant a >= 0;
  loop invariant l == \at(n, Pre) + 7;
  loop invariant n == \at(n, Pre) && m == \at(m, Pre);
  loop invariant v == \at(n, Pre) + 5*a;
  loop invariant l == \at(n, Pre) + 7 && n == \at(n, Pre) && m == \at(m, Pre) && a >= 0;
  loop invariant v == \at(n, Pre) + 5 * a;
  loop invariant p == 4 * a;
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns v, p, a;
*/
while (1) {
      v = v+5;
      p = p+4;
      a = a+1;
  }

}
