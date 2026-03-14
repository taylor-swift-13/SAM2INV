int main1(int d){
  int u5, z, aj4, ko, mphv;
  u5=d+15;
  z=0;
  aj4=(d%18)+5;
  ko=(d%15)+3;
  mphv=aj4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 0;
  loop invariant d == \at(d, Pre);
  loop invariant aj4 - ko == (\at(d, Pre) % 18 + 5) - (\at(d, Pre) % 15 + 3);
  loop assigns aj4, ko, d;
*/
while (aj4!=0) {
      aj4--;
      ko = ko - 1;
      d += z;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(d, Pre);
  loop invariant z <= 0;
  loop invariant u5 - z == \at(d, Pre) + 15;
  loop invariant z >= 0;
  loop invariant mphv >= \at(d, Pre) % 18 + 5;
  loop assigns u5, z, mphv;
*/
while (1) {
      if (!(z!=0)) {
          break;
      }
      u5 = u5 - 1;
      z = z - 1;
      mphv += z;
  }
}