int main1(){
  int xo4, bazd, z, w;
  xo4=1+5;
  bazd=2;
  z=1;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 <= bazd <= xo4;
  loop assigns bazd;
*/
while (bazd<xo4) {
      bazd = bazd + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w;
  loop invariant w <= z;
  loop invariant z == 1;
  loop assigns w;
*/
while (1) {
      w += 1;
      if (w>=z) {
          break;
      }
  }
/*@
  assert bazd == xo4;
  assert w == z && z == 1;
*/

}
