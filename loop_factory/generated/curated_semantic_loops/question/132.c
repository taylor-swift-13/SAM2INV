int main1(int b,int k){
  int y, u, x, r;

  y=61;
  u=0;
  x=0;
  r=u;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u<=y-2) {
      if (x+3<=y) {
          x = x+3;
      }
      else {
          x = y;
      }
  }
/*@
  assert !(u<=y-2) &&
         (u <= y - 2);
*/

}
