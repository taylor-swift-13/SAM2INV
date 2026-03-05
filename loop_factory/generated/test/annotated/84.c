int main1(int x,int k){
  int xyn, g, dod;
  xyn=52;
  g=0;
  dod=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= \at(x, Pre);
  loop invariant (x - \at(x, Pre)) % 2 == 0;
  loop invariant ((dod + 6) % 5 == 0) || (dod == xyn);
  loop invariant k - \at(k, Pre) >= ((x - \at(x, Pre)) / 2) * (-6);
  loop invariant k - \at(k, Pre) <= ((x - \at(x, Pre)) / 2) * xyn;
  loop invariant g == 0;
  loop invariant xyn == 52;
  loop invariant x >= \at(x, Pre) && (x - \at(x, Pre)) % 2 == 0
                   && k >= \at(k, Pre) + ((x - \at(x, Pre))/2) * (-6)
                   && k <= \at(k, Pre) + ((x - \at(x, Pre))/2) * xyn;
  loop invariant dod >= -6;
  loop invariant -6 <= dod <= xyn;
  loop assigns dod, x, k;
*/
while (1) {
      if (!(g<xyn)) {
          break;
      }
      if (dod+5<=xyn) {
          dod = dod + 5;
      }
      else {
          dod = xyn;
      }
      x += 2;
      k = k + dod;
  }
}