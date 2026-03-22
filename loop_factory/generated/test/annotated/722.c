int main1(){
  int r2, cd, cu9, imc, ge;
  r2=19;
  cd=r2+6;
  cu9=0;
  imc=(1%28)+10;
  ge=cd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= cu9;
  loop invariant cu9 <= 5;
  loop invariant imc == 11 - (cu9 * (cu9 - 1)) / 2;
  loop invariant ge >= 25;
  loop invariant r2 == 19;
  loop assigns imc, cu9, ge;
*/
while (imc>cu9) {
      imc = imc - cu9;
      cu9 = cu9 + 1;
      ge = ge+(imc%7);
  }
}