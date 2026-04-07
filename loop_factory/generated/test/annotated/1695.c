int main1(int q){
  int m9e, n, v7e, o5;
  m9e=108;
  n=0;
  v7e=n;
  o5=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o5 == 20 + n;
  loop invariant v7e == n;
  loop invariant q == \at(q, Pre) + (n + 1) / 2;
  loop invariant 0 <= n <= m9e;
  loop assigns n, o5, v7e, q;
*/
while (n < m9e) {
      n += 1;
      o5 += 1;
      v7e++;
      q = q+(n%2);
  }
}