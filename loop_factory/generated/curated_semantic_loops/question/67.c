int main1(int k,int n){
  int r, w, b, y;

  r=(k%21)+13;
  w=1;
  b=-2;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (b<r) {
      if (b<r) {
          b = b+1;
      }
      b = b+5;
      y = y+3;
  }
/*@
  assert !(b<r) &&
         (2*(y - 4) == b + 2);
*/

}
