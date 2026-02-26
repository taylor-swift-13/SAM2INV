int main1(int b,int m){
  int x, t, y, o;

  x=b;
  t=0;
  y=-2;
  o=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y % 2 == 0;
  loop invariant o % 2 == 0;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant x == b;
  loop invariant y <= 0;
  loop invariant o >= 0;
  loop invariant x == \at(b, Pre);
  loop invariant y != 0 || o != 0;
  loop invariant o - y >= 0;
  loop assigns y, o;
*/
while (y!=0&&o!=0) {
      if (y>o) {
          y = y-o;
      }
      else {
          o = o-y;
      }
  }

}
