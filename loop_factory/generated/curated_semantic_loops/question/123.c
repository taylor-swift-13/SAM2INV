int main1(int m,int n){
  int r, w, v, u;

  r=(n%8)+8;
  w=0;
  v=-5;
  u=4;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<r) {
      if (v<r) {
          v = v+1;
      }
      u = u+u;
  }
/*@
  assert !(v<r) &&
         (r == (n % 8) + 8);
*/

}
