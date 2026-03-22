int main1(){
  int fc, shf, jwi;
  fc=8;
  shf=-1;
  jwi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (shf % 2) != 0;
  loop invariant ((jwi + shf) - (fc + 1)) % 2 == 0;
  loop invariant ((jwi + shf) == (fc + 3)) || ((shf == -1) && (jwi == 0));
  loop invariant jwi % 2 == 0;
  loop assigns jwi, shf;
*/
while (shf<fc) {
      jwi = fc-shf;
      jwi = jwi + 1;
      shf += 2;
  }
}