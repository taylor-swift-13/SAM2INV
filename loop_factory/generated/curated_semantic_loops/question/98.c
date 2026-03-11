int main1(int p,int q){
  int r, u, v;

  r=(q%29)+5;
  u=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u<=r-1) {
      if (v<r+4) {
          v = v-v;
      }
      u = u+1;
  }
/*@
  assert !(u<=r-1) &&
         (r == (q % 29) + 5);
*/

}
