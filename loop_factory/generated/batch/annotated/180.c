int main1(int k,int n){
  int r, w, b, y;

  r=(k%21)+13;
  w=1;
  b=-2;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*(y - 4) == b + 2;
  loop invariant b >= -2;
  loop invariant b <= r + 5;
  loop invariant y >= 4;
  loop invariant r == (\at(k, Pre) % 21) + 13;
  loop invariant b + 2 == 2*(y - 4);
  loop invariant (y - 4) % 3 == 0;
  loop invariant k == \at(k,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant (b + 2) % 6 == 0;
  loop invariant r == (k % 21) + 13;
  loop invariant b - 2*y == -10;
  loop invariant b == 2*y - 10;

  loop assigns b, y;
*/
while (b<r) {
      if (b<r) {
          b = b+1;
      }
      b = b+5;
      y = y+3;
  }

}
