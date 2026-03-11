int main1(int m){
  int l, n, qd;
  l=(m%29)+14;
  n=l;
  qd=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qd >= l;
  loop invariant l == (\at(m, Pre) % 29) + 14;
  loop invariant n % 3 == l % 3;
  loop invariant qd == l + (l - n)/3;
  loop assigns qd, n;
*/
for (; n>=3; n = n - 3) {
      qd = qd + 1;
  }
}