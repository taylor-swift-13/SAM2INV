int main1(){
  int nn1, nd5z, swkr;
  nn1=1;
  nd5z=0;
  swkr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nd5z;
  loop invariant nd5z <= nn1;
  loop invariant (nd5z < nn1) ==> (nd5z + 1 == nn1 && swkr == 0);
  loop invariant (nd5z == 0 && swkr == 0) || (nd5z == nn1 && swkr == 1);
  loop assigns swkr, nd5z;
*/
while (nd5z < nn1) {
      swkr = swkr + ((nd5z++ * 2 < nn1) ? 1 : -1);
      nd5z = nn1;
  }
}