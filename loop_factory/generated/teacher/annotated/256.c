int main1(int b,int q){
  int h, r, y;

  h=50;
  r=0;
  y=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant h == 50;
  loop invariant r % 3 == 0;
  loop invariant r <= h;
  loop invariant y == b + r/3;
  loop invariant r == 3*(y - b);
  loop invariant y >= b;

  loop invariant 0 <= r;
  loop invariant y == \at(b, Pre) + r/3;
  loop invariant 3*(y - \at(b, Pre)) == r;
  loop invariant r >= 0;
  loop assigns r, y;
*/
while (r<=h-3) {
      if (r+7<=h+h) {
          y = y+1;
      }
      else {
          y = y+1;
      }
      r = r+3;
  }

}
