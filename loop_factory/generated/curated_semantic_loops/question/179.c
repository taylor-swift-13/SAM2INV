int main1(int b,int n){
  int r, z, u;

  r=(n%34)+11;
  z=r;
  u=r;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (z>3) {
      if (z+5<=u+r) {
          u = u+4;
      }
      z = z-4;
  }
/*@
  assert !(z>3) &&
         (r == (\at(n, Pre) % 34) + 11);
*/

}
