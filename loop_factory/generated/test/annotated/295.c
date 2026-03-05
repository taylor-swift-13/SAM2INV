int main1(int r){
  int wpus, vrqi, nehb;
  wpus=r-1;
  vrqi=0;
  nehb=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wpus == \at(r, Pre) - 1 && (nehb == 1 || nehb == 2 || nehb == 4 || nehb == 8);
  loop invariant vrqi >= 0 && (wpus >= 0 ==> vrqi <= wpus) && r >= \at(r, Pre) + 2*vrqi && r <= \at(r, Pre) + 8*vrqi;
  loop invariant ((r - \at(r, Pre)) % 2) == 0;
  loop assigns r, vrqi, nehb;
*/
while (vrqi<wpus) {
      if (nehb>=5) {
          nehb = -1;
      }
      if (nehb<=1) {
          nehb = 1;
      }
      nehb = nehb + nehb;
      vrqi = vrqi + 1;
      r = r + nehb;
  }
}