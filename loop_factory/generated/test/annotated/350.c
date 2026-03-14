int main1(){
  int ky, t9, qlh, pse, qw;
  ky=1-7;
  t9=ky;
  qlh=(1%18)+5;
  pse=(1%15)+3;
  qw=qlh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qlh - pse == 2;
  loop invariant qlh >= 0;
  loop invariant t9 == ky;
  loop assigns pse, qlh, qw;
*/
while (qlh!=0) {
      pse -= 1;
      qlh -= 1;
      qw = qw+ky-t9;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ky == -6;
  loop assigns pse, qlh, qw;
*/
while (pse<ky) {
      pse++;
      qw++;
      qlh += qw;
  }
}