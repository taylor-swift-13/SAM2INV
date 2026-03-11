int main1(int m,int p){
  int l, z, x, r;

  l=67;
  z=1;
  x=0;
  r=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x % 4 == 0;
  loop invariant x >= 0;
  loop invariant r >= 2;
  loop invariant r % 2 == 0;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant x % 4 == 0 && x == 4 * (x / 4);
  loop invariant r >= 2 && r % 2 == 0;
  loop invariant x % 8 == 0;
  loop invariant l == 67;

  loop invariant x < l/2 ==> r == 2;
  loop invariant x % 8 == 0 && x >= 0 && r % 2 == 0;
  loop invariant r >= 2 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant x < 4*l + 8;
  loop invariant r % 2 == 0 && r >= 2;
  loop invariant x <= 4*l + 8 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant x >= 0 && x % 4 == 0 && r >= 2 && r % 2 == 0;
  loop assigns r, x;
*/
while (x<l) {
      if (x>=l/2) {
          r = r+2;
      }
      x = x+1;
      x = x*4+4;
  }
/*@
  assert !(x<l) &&
         (x % 4 == 0);
*/


}
