int main1(int n,int p){
  int w, y, v, r;

  w=n-10;
  y=0;
  v=4;
  r=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && v >= 0;
  loop invariant r >= 0 && v + r <= 4;
  loop invariant w == n - 10;
  loop invariant v >= 0;
  loop invariant r >= 0;
  loop invariant v <= 4;
  loop invariant r == 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v > 0;

  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && v % 4 == 0 && r % 4 == 0;
  loop invariant v + r <= 4;
  loop invariant w == \at(n, Pre) - 10 && n == \at(n, Pre) && p == \at(p, Pre) && v >= 0 && r >= 0;
  loop invariant v != 0 || r == 0;
  loop invariant n == \at(n,Pre) && p == \at(p,Pre) && w == \at(n,Pre) - 10;
  loop invariant w == \at(n,Pre) - 10;
  loop assigns v, r;
*/
while (v!=0&&r!=0) {
      if (v>r) {
          v = v-r;
      }
      else {
          r = r-v;
      }
  }
/*@
  assert !(v!=0&&r!=0) &&
         (n == \at(n, Pre) && p == \at(p, Pre) && v >= 0);
*/


}
