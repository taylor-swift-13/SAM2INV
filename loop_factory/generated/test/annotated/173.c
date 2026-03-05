int main1(int x){
  int b1, qd, nfhw;
  b1=11;
  qd=b1;
  nfhw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nfhw >= 0;
  loop invariant x >= \at(x, Pre);
  loop invariant (x - \at(x, Pre)) % b1 == 0;
  loop invariant qd == 11;
  loop invariant x <= \at(x, Pre) + 11 * nfhw;
  loop invariant b1 >= 0;
  loop assigns nfhw, x;
*/
while (qd>0) {
      nfhw = nfhw + 1;
      nfhw = nfhw+nfhw*nfhw*nfhw*nfhw;
      x = x + b1;
  }
}