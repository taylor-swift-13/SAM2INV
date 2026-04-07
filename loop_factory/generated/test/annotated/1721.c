int main1(){
  int nq, xi, ii, fe, owm;
  nq=71;
  xi=0;
  ii=0;
  fe=0;
  owm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fe == xi;
  loop invariant 0 <= xi;
  loop invariant xi <= nq;
  loop invariant xi == ii;
  loop invariant xi == owm;
  loop assigns xi, ii, owm, fe;
*/
while (xi < nq) {
      xi = xi + 1;
      ii = ii + 1;
      owm = owm + 1;
      fe += 1;
  }
}