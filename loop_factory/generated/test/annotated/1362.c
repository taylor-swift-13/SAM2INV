int main1(){
  int n2, ba, u;
  n2=1;
  ba=n2;
  u=ba;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n2 == 1;
  loop invariant ba % 3 == 1;
  loop invariant u % 3 == 1;
  loop invariant ba <= n2;
  loop invariant u >= 1;
  loop assigns ba, u;
*/
for (; ba>2; ba = ba - 3) {
      u = u*4;
  }
}