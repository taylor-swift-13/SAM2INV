int main1(){
  int xpp, uqr, duj, p, ni;
  xpp=1;
  uqr=0;
  duj=1;
  p=1;
  ni=xpp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 1 + (duj - 1) * (duj - 1);
  loop invariant duj >= 1;
  loop invariant p == 1 + (duj - 1) * (duj - 1) &&
                   ni == 1 + (duj - 1) * xpp;
  loop invariant duj <= xpp + 1;
  loop invariant ni == duj;
  loop invariant xpp == 1;
  loop assigns p, duj, ni;
*/
while (duj<=xpp) {
      p = p+2*duj-1;
      duj += 1;
      ni += xpp;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant duj >= 0;
  loop invariant xpp >= 0;
  loop invariant duj % 8 == 2;
  loop invariant uqr == xpp * ((duj - 2) / 8);
  loop assigns p, duj, uqr;
*/
while (1) {
      if (!(duj<xpp)) {
          break;
      }
      p = xpp-duj;
      duj += 8;
      uqr += xpp;
  }
}