int main1(int m,int n){
  int r, u, v, p;

  r=53;
  u=r;
  v=r;
  p=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v % 53 == 0;
  loop invariant u % 2 == 1;
  loop invariant u <= 53;
  loop invariant (53 - u) >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant r == 53;
  loop invariant 1 <= u <= 53;
  loop invariant (u % 2) == 1;
  loop invariant u >= 1;
  loop invariant (u % 2 == 1);
  loop invariant (v % 53 == 0);
  loop invariant r == 53 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant 1 <= u && u <= r && ((r - u) % 2) == 0;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre) && r == 53 && 1 <= u && u <= 53;
  loop invariant u % 2 == 1 && v >= 53 && v % 53 == 0;
  loop invariant u >= 1 && u <= r && (r - u) % 2 == 0;
  loop invariant u >= 1 && u <= r;
  loop invariant u % 2 == r % 2;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant 1 <= u && u <= 53;
  loop assigns u, v;
*/
while (u>1) {
      v = v*2;
      u = u-2;
  }

}
