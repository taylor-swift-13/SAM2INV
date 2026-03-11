int main1(int m,int n){
  int y, w, v, h;

  y=n+19;
  w=1;
  v=0;
  h=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant -v <= h <= v;
  loop invariant v >= 0 && y == \at(n,Pre) + 19 && m == \at(m,Pre) && n == \at(n,Pre);
  loop invariant (m == \at(m, Pre)) && (n == \at(n, Pre)) && (y == n + 19);
  loop invariant (0 <= v) && (((h + v) % 2) == 0);
  loop invariant v >= 0;
  loop invariant -v <= h && h <= v;
  loop invariant (y/2 <= 0) ==> h == -v;
  loop invariant (v <= y/2) ==> h == v;
  loop invariant (y/2 > 0 && v > y/2) ==> h == 2*(y/2) - v;
  loop invariant h <= v;

  loop invariant 0 <= v;

  loop invariant y == n + 19;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant n == \at(n, Pre) && m == \at(m, Pre) && y == n + 19 && v >= 0 && (v <= y || v == 0);


  loop assigns h, v;
*/
while (v<y) {
      if (v<y/2) {
          h = h+1;
      }
      else {
          h = h-1;
      }
      v = v+1;
  }
/*@
  assert !(v<y) &&
         (-v <= h <= v);
*/


}
