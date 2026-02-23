int main1(int n){
  int j, t, q, v;

  j=n+3;
  t=0;
  q=t;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(n, Pre) + 3;
  loop invariant q == 0;
  loop invariant v == 0;
  loop invariant t % 3 == 0;
  loop invariant t >= 0;
  loop invariant (t % 3 == 0);
  loop invariant t >= 0 && (t <= j || t == 0) && j == \at(n, Pre) + 3 && n == \at(n, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant j == n + 3;

  loop assigns t, v;
*/
while (t<=j-3) {
      v = v+v;
      v = v+q;
      t = t+3;
  }

}
