int main1(int z){
  int yzam, a, nu, ltp, ls, bif;
  yzam=63;
  a=2;
  nu=29;
  ltp=0;
  ls=1;
  bif=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ls == a - 1;
  loop invariant nu + ltp == 29;
  loop invariant (nu >= 0);
  loop invariant (a <= yzam);
  loop invariant z == \at(z, Pre);
  loop assigns a, bif, ls, ltp, nu;
*/
while (1) {
      if (!(nu>0&&a<yzam)) {
          break;
      }
      if (nu<=ls) {
          bif = nu;
      }
      else {
          bif = ls;
      }
      a++;
      ltp = ltp + bif;
      nu = nu - bif;
      ls++;
  }
}