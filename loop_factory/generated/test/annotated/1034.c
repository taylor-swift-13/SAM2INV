int main1(){
  int dwv, x, xqe, jh, sj;
  dwv=1*3;
  x=0;
  xqe=0;
  jh=0;
  sj=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jh == xqe*(xqe - 1) / 2;
  loop invariant sj == 2 + xqe*(xqe - 1)*(xqe + 1) / 6;
  loop invariant 0 <= xqe <= dwv;
  loop invariant dwv == 3;
  loop assigns jh, xqe, sj;
*/
while (xqe<dwv) {
      jh += xqe;
      xqe++;
      sj += jh;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sj >= 2;
  loop invariant sj - dwv * jh == -3;
  loop invariant dwv <= xqe;
  loop invariant sj == 6 + (dwv - 3) * jh;
  loop assigns x, dwv, sj;
*/
while (dwv<xqe) {
      x = xqe-dwv;
      sj += jh;
      dwv++;
  }
}