int main1(int a,int p){
  int n, j, y;

  n=58;
  j=n;
  y=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 4*j - 174;
  loop invariant 0 <= j;
  loop invariant j <= n;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant n == 58;
  loop invariant j >= 0;
  loop invariant j <= 58;
  loop invariant 0 <= j <= 58;
  loop invariant y == 4*j - 3*n;
  loop assigns y, j;
*/
while (j>0) {
      if (j+2<=n+n) {
          y = y-4;
      }
      j = j-1;
  }

}
