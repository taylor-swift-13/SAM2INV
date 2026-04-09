int main1(){
  int gof, nqg, t0ii, xf, km;
  gof=1;
  nqg=0;
  t0ii=nqg;
  xf=-1;
  km=nqg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nqg;
  loop invariant nqg <= gof;
  loop invariant km == nqg * t0ii;
  loop invariant t0ii == 0;
  loop invariant xf == (-1 + (nqg * (nqg + 1)) / 2);
  loop assigns nqg, xf, km;
*/
while (nqg<gof) {
      nqg += 1;
      xf += nqg;
      km += t0ii;
  }
}