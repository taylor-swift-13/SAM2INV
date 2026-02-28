int main1(int m,int q){
  int n, t, f;

  n=(q%38)+9;
  t=n;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (q % 38) + 9;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant (t > 0) ==> (f == q + 5 || f == n);
  loop invariant n == (\at(q, Pre) % 38) + 9;

  loop invariant (t == n && f == n) || (t < n && f == q + 5);
  loop invariant n == ((\at(q, Pre) % 38) + 9);
  loop invariant n == \at(q, Pre) % 38 + 9;

  loop invariant (t < n) ==> f == q + 5;
  loop invariant (t == n) ==> f == n;
  loop assigns f, t;
*/
while (t>0) {
      f = q+5;
      t = t-1;
  }

}
