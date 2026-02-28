int main1(int a,int n){
  int b, u, y, s;

  b=49;
  u=0;
  y=n;
  s=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant y >= n;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (s == y - 3) || (s == 1 && y == n);
  loop invariant (s <= y) || (s == 1 && y == n);
  loop invariant ((s == 1 && y == n) || (s == y - 3));
  loop invariant ((y - n) % 3 == 0);
  loop invariant (y - n) % 3 == 0;
  loop invariant y >= \at(n,Pre);

  loop assigns s, y;
*/
while (1) {
      s = y;
      y = y+2;
      y = y+1;
  }

}
