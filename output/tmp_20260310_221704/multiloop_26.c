int main1(){
  int n5, vsl8, qbv8;
  n5=(1%20)+5;
  vsl8=(1%20)+5;
  qbv8=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n5 == qbv8;
  loop invariant 0 <= n5 <= 6;
  loop invariant 0 <= vsl8;
  loop invariant vsl8 >= qbv8;
  loop assigns n5, vsl8, qbv8;
*/
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


  int __aux_9=0;
  while (__aux_9 < 2) { __aux_9 = __aux_9 + 1; }
}