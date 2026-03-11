int main1(){
  int n5, vsl8, qbv8;
  n5=(1%20)+5;
  vsl8=(1%20)+5;
  qbv8=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (n5>=1) {
      if (vsl8>0) {
          if (qbv8>0) {
              n5 -= 1;
              vsl8 -= 1;
              qbv8 -= 1;
          }
      }
      vsl8++;
  }
/*@
  assert !(n5>=1) &&
         (n5 == qbv8);
*/

}