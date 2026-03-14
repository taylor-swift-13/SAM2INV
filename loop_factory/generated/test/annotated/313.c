int main1(){
  int fz, d3, xab, nug, fq;
  fz=20;
  d3=fz;
  xab=d3;
  nug=1;
  fq=d3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nug == 1 + xab * (((d3 * (d3 - 1)) / 2) - 190);
  loop invariant d3 >= 20;
  loop invariant xab == 20;
  loop invariant fz == 20;
  loop invariant nug >= 1;
  loop assigns nug, d3;
*/
while (d3-2>=0) {
      nug = nug+xab*d3;
      d3++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fq == xab;
  loop invariant d3 >= xab;
  loop invariant d3 >= 20;
  loop assigns xab, fq;
*/
while (xab<d3) {
      xab = xab + 1;
      fq += 1;
  }
}