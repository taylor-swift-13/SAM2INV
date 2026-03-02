int main1(int m,int q){
  int n, v, r;

  n=m-5;
  v=0;
  r=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == m - 5 && m == \at(m, Pre) && q == \at(q, Pre) && v >= 0;
  loop invariant n <= m - 5 && n >= m - 5;
  loop invariant n == \at(m, Pre) - 5 && m == \at(m, Pre) && q == \at(q, Pre) && v >= 0;
  loop invariant (v > 0) ==> (r >= 0);
  loop invariant n == m - 5 && m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant v >= 0 && r >= n;
  loop invariant n == \at(m, Pre) - 5;
  loop invariant m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant v >= 0;
  loop invariant (v == 0 ==> r == n);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == m - 5;

  loop invariant n == m - 5 && v >= 0;
  loop invariant (v == 0 ==> r == n) && (v > 0 ==> r >= 0);
  loop invariant v == 0 ==> r == n;
  loop invariant (v == 0) ==> (r == n);
  loop invariant m == \at(m, Pre) && q == \at(q, Pre) && n == \at(m, Pre) - 5;
  loop assigns r, v;
*/
while (1) {
      r = r*r;
      v = v+1;
  }

}
