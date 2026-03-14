int main1(){
  int ry, k, trl, ys, gge, xds;
  ry=1+15;
  k=4;
  trl=ry;
  ys=0;
  gge=0;
  xds=ry;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (k == 4);
  loop invariant (trl == 16);
  loop invariant (ys % trl == 0);
  loop invariant (0 <= ys);
  loop invariant (gge >= 0);
  loop invariant (ry >= k);
  loop invariant xds >= 0;
  loop assigns ys, gge, xds, ry;
*/
while (k+1<=ry) {
      ys += trl;
      gge += ys;
      xds = xds+(ys%7);
      ry = (k+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gge >= 0;
  loop invariant ys >= 0;
  loop invariant k % 2 == 0;
  loop invariant k >= 4;
  loop assigns gge, ys, k, xds;
*/
while (1) {
      if (!(xds-6>=0)) {
          break;
      }
      gge = gge + k;
      ys = ys + xds;
      k += 2;
      xds += 1;
  }
}