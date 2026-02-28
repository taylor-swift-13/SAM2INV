int main1(int a,int q){
  int n, k, y;

  n=24;
  k=n;
  y=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k <= 24;
  loop invariant k >= 0;
  loop invariant k % 3 == 0;
  loop invariant y % 24 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant y >= 24;
  loop invariant n == 24;
  loop invariant 0 <= k;
  loop invariant k <= n;

  loop assigns y, k;
*/
while (k>=3) {
      y = y+y;
      k = k-3;
  }

}
