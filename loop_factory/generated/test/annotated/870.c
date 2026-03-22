int main1(){
  int tv67, k, abi, rn;
  tv67=1;
  k=1;
  abi=tv67;
  rn=tv67;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant abi == rn*rn;
  loop invariant tv67 <= 3 * k;
  loop invariant 0 <= rn;
  loop invariant 0 <= tv67;
  loop assigns rn, abi, tv67;
*/
while (k*3<=tv67) {
      rn += 1;
      abi = rn*rn;
      tv67 = ((k*3))+(-(1));
  }
}