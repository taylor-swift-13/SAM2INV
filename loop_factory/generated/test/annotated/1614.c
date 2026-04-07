int main1(int d){
  int r, fw, nvk, u7i, zcg;
  r=d-10;
  fw=r;
  nvk=0;
  u7i=1;
  zcg=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(d, Pre) - 10;
  loop invariant (nvk == 0) ==> (fw == r);
  loop invariant (nvk > 0) ==> (fw == 0);
  loop invariant nvk >= 0;
  loop invariant u7i == 1 + nvk*(nvk+1)/2;
  loop invariant zcg == -8 + nvk*(nvk+1)/2;
  loop invariant r == d - 10;
  loop invariant ((nvk == 0 && fw == d - 10 && u7i == 1 && zcg == -8) ||
                    (nvk == 1 && fw == 0 && u7i == 2 && zcg == -7));
  loop assigns nvk, u7i, zcg, fw;
*/
while (fw>0) {
      nvk += 1;
      u7i = u7i + nvk;
      zcg = zcg + nvk;
      fw = 0;
  }
}