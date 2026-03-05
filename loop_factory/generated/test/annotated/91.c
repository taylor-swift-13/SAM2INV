int main1(){
  int h2, ngg, rkt;
  h2=1+21;
  ngg=0;
  rkt=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rkt == 12 + 7*ngg;
  loop invariant ngg <= h2;
  loop invariant 0 <= ngg;
  loop invariant h2 == 1 + 21;
  loop assigns rkt, ngg;
*/
while (ngg<h2) {
      rkt = rkt + 7;
      ngg++;
  }
}