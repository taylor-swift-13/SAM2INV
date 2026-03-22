int main1(){
  int cbs, z0, z5i;
  cbs=1;
  z0=-6;
  z5i=cbs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z0 <= cbs;
  loop invariant z0 >= -6;
  loop invariant cbs == 1;
  loop assigns z0;
*/
while (1) {
      if (!(z0+1<=cbs)) {
          break;
      }
      z0 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z5i + cbs - z0 == 1;
  loop invariant z5i >= 0;
  loop invariant z0 >= 1;
  loop invariant z5i <= 1;
  loop assigns z5i, z0, cbs;
*/
while (z5i>z0) {
      z5i -= z0;
      z0 += 1;
      cbs += z0;
  }
}