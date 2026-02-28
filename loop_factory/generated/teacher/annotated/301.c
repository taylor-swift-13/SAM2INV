int main1(int b,int m){
  int x, t, y, o;

  x=b;
  t=0;
  y=x;
  o=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((x - y) % 2) == 0;
  loop invariant y <= x;
  loop invariant x == b;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant y >= b;
  loop invariant (4*o) == (y*y) - 2*y + 2*b - b*b - 8;
  loop invariant o >= -2;
  loop invariant ((y - x) % 2) == 0;
  loop invariant 4*o == y*y + 2*y - x*x - 2*x - 8;
  loop invariant x == \at(b, Pre);
  loop assigns y, o;
*/
while (y<x) {
      if (y<x) {
          y = y+1;
      }
      y = y+1;
      o = o+y;
  }

}
