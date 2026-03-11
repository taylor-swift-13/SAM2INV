int main1(){
  int xo4, bazd, z, w;
  xo4=1+5;
  bazd=2;
  z=1;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (bazd<xo4) {
      bazd = bazd + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */

while (1) {
      w += 1;
      if (w>=z) {
          break;
      }
  }
/*@
  assert bazd == xo4;
*/
/*@
  assert w >= z && z == 1;
*/

}
