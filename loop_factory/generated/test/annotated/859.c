int main1(){
  int txb, mm, j2, xf;
  txb=1*2;
  mm=txb;
  j2=-5;
  xf=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mm == 2;
  loop invariant txb == 2;
  loop invariant (xf == 0) ==> (j2 == -5);
  loop invariant (xf >= 1) ==> (j2 == xf*xf);
  loop invariant xf >= 0;
  loop assigns xf, j2, mm;
*/
while (mm>=3) {
      xf = xf + 1;
      j2 = xf*xf;
      mm = 2;
  }
}