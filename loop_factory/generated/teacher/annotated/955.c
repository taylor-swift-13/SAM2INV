int main1(int b,int m){
  int r, t, v, y;

  r=49;
  t=2;
  v=m;
  y=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == 49;
  loop invariant y >= -5;
  loop invariant v == m || v == y*y + 1;
  loop invariant ( (y == -5 && v == m) || (v == y*y + 1) );
  loop invariant b == \at(b, Pre) && m == \at(m, Pre) && r == 49;
  loop invariant (y == -5) ==> (v == \at(m, Pre)) && (y != -5) ==> (v == y*y + 1);
  loop invariant (b == \at(b, Pre)) && (m == \at(m, Pre)) && (y >= -5);
  loop invariant b == \at(b, Pre) && m == \at(m, Pre) && y >= -5;
  loop invariant (y == -5 && v == m) || (v == y*y + 1);
  loop invariant v == y*y + 1 || v == m;
  loop invariant (y != -5) ==> (v == y*y + 1);
  loop assigns y, v;
*/
while (1) {
      y = y+1;
      v = y*y;
      v = v+1;
  }

}
