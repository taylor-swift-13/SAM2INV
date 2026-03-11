int main1(int a,int p){
  int m, y, b;

  m=26;
  y=m;
  b=y;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (y>=1) {
      b = b+4;
      if (y<m+5) {
          b = b+y;
      }
  }
/*@
  assert !(y>=1) &&
         (y >= 1);
*/

}
