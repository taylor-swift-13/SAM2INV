int main1(int u){
  int md, z2, nb, dcq1, dxx;
  md=u*2;
  z2=0;
  nb=1;
  dcq1=1;
  dxx=md;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant md == 2 * u;
  loop invariant z2 >= 0;
  loop invariant dcq1 == 1 + 2 * z2;
  loop invariant nb == (z2 + 1) * (z2 + 1);
  loop invariant dxx == md + z2 * (z2 + 1);
  loop assigns z2, dcq1, nb, dxx;
*/
while (1) {
      if (!(nb<=md)) {
          break;
      }
      z2++;
      dcq1 += 2;
      nb = nb + dcq1;
      dxx = dxx+z2+z2;
  }
}