int main1(int z){
  int a, hzv, ykk, xb8a, cwu, vt, wk;
  a=27;
  hzv=0;
  ykk=0;
  xb8a=0;
  cwu=0;
  vt=8;
  wk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ykk == 3*(vt - 8);
  loop invariant ykk == cwu;
  loop invariant cwu == xb8a;
  loop invariant wk == ((vt - 8) * (vt + 9)) / 2;
  loop invariant ykk <= a;
  loop invariant vt >= 8;
  loop assigns vt, ykk, cwu, xb8a, wk;
*/
while (1) {
      if (!(ykk<a)) {
          break;
      }
      vt = vt + 1;
      ykk = ykk + 3;
      cwu = cwu + 3;
      xb8a = xb8a + 3;
      wk += hzv;
      wk += vt;
  }
}