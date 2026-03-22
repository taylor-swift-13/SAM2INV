int main1(int m){
  int mi, zsz, vi, msv, xjmc, xlzq, lqs4;
  mi=(m%38)+17;
  zsz=0;
  vi=1;
  msv=1;
  xjmc=0;
  xlzq=mi;
  lqs4=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre) + mi * zsz;
  loop invariant msv == 2*zsz + 1;
  loop invariant vi  == (zsz + 1) * (zsz + 1);
  loop invariant lqs4 == 4;
  loop invariant xjmc == 0;
  loop invariant xlzq == mi;
  loop invariant zsz >= 0;
  loop invariant xlzq == \at(m, Pre) % 38 + 17;
  loop assigns m, msv, zsz, xjmc, lqs4, xlzq, vi;
*/
while (vi<=mi) {
      msv += 2;
      zsz += 1;
      xjmc = xjmc*2;
      m += mi;
      vi += msv;
      lqs4 = lqs4%5;
      xlzq += xjmc;
  }
}