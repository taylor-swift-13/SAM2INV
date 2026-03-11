int main1(int a,int m){
  int x, j, i, b;

  x=35;
  j=x;
  i=5;
  b=3;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j-4>=0) {
      if (i+6<=x) {
          i = i+6;
      }
      else {
          i = x;
      }
  }
/*@
  assert !(j-4>=0) &&
         (m == \at(m, Pre));
*/

}
