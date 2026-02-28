int main1(int k,int n){
  int r, w, b, y;

  r=(k%21)+13;
  w=1;
  b=-2;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 4;
  loop invariant (y - 4) % 3 == 0;
  loop invariant w == 1;
  loop invariant r == (\at(k, Pre) % 21) + 13;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (w < r/2) ==> (6*b == y*y + 7*y - 56);
  loop invariant (w >= r/2) ==> (b == 2*y - 10);
  loop invariant y % 3 == 1;
  loop invariant b >= -2;

  loop invariant r == \at(k, Pre) % 21 + 13;
  loop invariant b - 2*y >= -10;

  loop assigns b, y;
*/
while (w<=r-1) {
      if (w<r/2) {
          b = b+y;
      }
      else {
          b = b+1;
      }
      b = b+5;
      y = y+3;
  }

}
