int main1(int a){
  int ufl, yp, g77;
  ufl=(a%20)+5;
  yp=(a%20)+5;
  g77=(a%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ufl == yp;
  loop invariant yp == g77;
  loop invariant ufl <= ((\at(a,Pre) % 20) + 5);
  loop invariant a >= \at(a,Pre);
  loop assigns ufl, yp, g77, a;
*/
while (1) {
      if (!(ufl>=1)) {
          break;
      }
      if (yp>0) {
          if (g77>0) {
              ufl--;
              yp = yp - 1;
              g77--;
          }
      }
      a = a + ufl;
  }
}