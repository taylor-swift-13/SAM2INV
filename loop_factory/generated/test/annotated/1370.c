int main1(){
  int j7w, zdx, y9r, tp35;
  j7w=(1%33)+14;
  zdx=3;
  y9r=zdx;
  tp35=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j7w == 15;
  loop invariant zdx <= j7w;
  loop invariant zdx >= 3;
  loop invariant y9r == 3;
  loop invariant tp35 == 0;
  loop assigns y9r, zdx;
*/
while (1) {
      if (!(zdx+1<=j7w)) {
          break;
      }
      y9r += tp35;
      zdx = zdx + 1;
  }
}