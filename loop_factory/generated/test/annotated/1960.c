int main1(){
  int xut, jrx3, sq, b, fc;
  xut=51;
  jrx3=0;
  sq=0;
  b=jrx3;
  fc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jrx3;
  loop invariant jrx3 <= xut;
  loop invariant sq == (b * jrx3);
  loop invariant (2 * fc) == (b * jrx3 * (jrx3 + 1));
  loop invariant b == 0;
  loop assigns jrx3, sq, fc;
*/
while (jrx3 < xut) {
      jrx3++;
      sq += b;
      fc += sq;
  }
}