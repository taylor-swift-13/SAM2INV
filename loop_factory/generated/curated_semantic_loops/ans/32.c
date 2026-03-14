int main1(int k,int p){
  int r, c, v, y, l, s;

  r=30;
  c=r+3;
  v=r;
  y=-8;
  l=k;
  s=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 30;
  loop invariant c == r + 3;
  loop invariant l == k;
  loop invariant v <= r;
  loop invariant y == -8 || y == k;
  loop invariant (v - r) % (c + 1) == 0;
  loop invariant v - y >= 38;
  loop invariant v >= r;
  loop invariant (y == -8) || (y == l);
  loop invariant (c == r + 3);
  loop invariant ((v - r) % 34 == 0);
  loop invariant y == -8 || y == l;
  loop invariant k == \at(k, Pre);
  loop assigns y, v;
*/
while (1) {
      if (v>=r) {
          break;
      }
      if (l<=y) {
          y = l;
      }
      v = v+1;
      v = v+c;
  }
/*@
  assert (r == 30);
*/



  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y <= 0;
  loop invariant v >= r;
  loop invariant r == 30;
  loop assigns y, v;
*/
  while (y < 0) {
      y = y + 1;
      v = v + 1;
  }
/*@
  assert !(y < 0) &&
         (y == 0);
*/
}
