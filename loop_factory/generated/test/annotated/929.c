int main1(int q){
  int n8, mis, oegz, yk;
  n8=47;
  mis=0;
  oegz=0;
  yk=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= mis <= n8;
  loop invariant yk == -6 + mis * (mis + 1) / 2;
  loop invariant (mis < 24) ==> (oegz == 0);
  loop invariant (mis <= n8/2) ==> (oegz == 0);
  loop assigns mis, oegz, yk;
*/
while (mis<=n8-1) {
      if (!(!(mis>=n8/2))) {
          oegz += 4;
      }
      mis += 1;
      yk = yk + mis;
  }
}