int main1(int a,int p){
  int n, j, y;

  n=58;
  j=n;
  y=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == y;
  loop invariant n == 58;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j <= n;
  loop invariant j >= 0;
  loop invariant j <= 114;
  loop invariant y == j;
  loop invariant j % 4 == 2;
  loop invariant j >= 2;
  loop assigns j, y;
*/
while (j>3) {
      if (j+2<=n+n) {
          y = y-4;
      }
      j = j-4;
  }

}
