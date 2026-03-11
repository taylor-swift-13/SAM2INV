int main1(int n){
  int r, c, y;

  r=50;
  c=r;
  y=r;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (c-2>=0) {
      c = c-2;
  }
/*@
  assert !(c-2>=0) &&
         (0 <= c);
*/

}
