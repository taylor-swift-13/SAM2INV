int main1(int a,int q){
  int x, u, d;

  x=q;
  u=4;
  d=8;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u+1<=x) {
      d = d+2;
      d = u%5;
  }
/*@
  assert !(u+1<=x) &&
         (u == 4);
*/

}
