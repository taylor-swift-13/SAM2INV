int main1(){
  int y, dj, shy, leo, txo;
  y=51;
  dj=0;
  shy=1;
  leo=1;
  txo=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant shy == (dj + 1) * (dj + 1);
  loop invariant leo == 1 + 2 * dj;
  loop invariant dj >= 0;
  loop invariant txo == 1 + (dj*(dj-1)*(2*dj-1))/6 + 3*dj*dj + 4*dj;
  loop assigns dj, leo, shy, txo;
*/
while (shy<=y) {
      dj += 1;
      leo += 2;
      shy += leo;
      txo = txo+leo+shy;
  }
}