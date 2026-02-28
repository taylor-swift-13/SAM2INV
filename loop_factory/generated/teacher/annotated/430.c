int main1(int a,int n){
  int b, u, y, s;

  b=49;
  u=0;
  y=n;
  s=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == 49;
  loop invariant u == 0;

  loop invariant ((n <= y && y <= b) || (b <= y && y <= n));
  loop invariant y <= b || y == n;
  loop assigns y;
*/
while (u+1<=b) {
      if (y+3<=b) {
          y = y+3;
      }
      else {
          y = b;
      }
      y = y+u;
  }

}
