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
  loop invariant s >= 0;
  loop invariant s <= 1;
  loop invariant u == 0;
  loop invariant (s == 0) || (s == 1);
  loop invariant (n >= 0) ==> (y >= 0);
  loop invariant (n <= 0) ==> (y <= 0);

  loop invariant (y * n) >= 0;
  loop assigns y, s;
*/
while (1) {
      y = y*3;
      s = s/3;
      y = y+u;
  }

}
