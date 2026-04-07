int main1(){
  int i5, nxkr, urur, zr, wb, lo;
  i5=58;
  nxkr=0;
  urur=nxkr;
  zr=0;
  wb=i5;
  lo=i5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zr == -(nxkr * nxkr);
  loop invariant lo == 58 + (nxkr * (nxkr + 1)) / 2;
  loop invariant urur == 58 * nxkr;
  loop invariant urur == wb * nxkr;
  loop invariant lo == i5 + nxkr * (nxkr + 1) / 2;
  loop invariant 0 <= nxkr;
  loop invariant nxkr <= i5;
  loop assigns zr, nxkr, lo, urur;
*/
while (nxkr < i5) {
      zr = zr - (2*nxkr + 1);
      nxkr++;
      lo = lo + nxkr;
      urur = urur + wb;
  }
}