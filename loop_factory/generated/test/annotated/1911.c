int main1(){
  int os, yeo, oqj, vc, w7, bc, rh, qlb;
  os=1+19;
  yeo=0;
  oqj=12;
  vc=14;
  w7=0;
  bc=-2;
  rh=0;
  qlb=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= yeo && yeo <= os);
  loop invariant (oqj + vc == 26);
  loop invariant (w7 == (yeo % 2));
  loop invariant (qlb == 5 + 3 * yeo);
  loop invariant (bc == -2 + (yeo * (yeo + 1)) / 2 + 4 * yeo);
  loop invariant (0 <= rh && rh <= (os - 7) && rh <= yeo && ((yeo <= (os - 7)) ==> (rh == yeo)));
  loop invariant 0 <= yeo && yeo <= os;
  loop invariant oqj + vc == 26;
  loop invariant w7 == (yeo % 2);
  loop invariant qlb == 5 + 3*yeo;
  loop invariant bc == -2 + (yeo*(yeo+1))/2 + 4*yeo;
  loop invariant ((yeo <= 13 && rh == yeo) || (yeo > 13 && rh == 13));
  loop invariant (yeo <= os) && (0 <= yeo) && ((w7 == 0) || (w7 == 1)) && (rh <= os - 7);
  loop invariant 0 <= w7 && w7 <= 1 && w7 == (yeo % 2);
  loop invariant (oqj + vc) == 26;
  loop invariant bc == -2 + ((yeo * (yeo + 1)) / 2) + 4 * yeo;
  loop invariant 0 <= rh && rh <= yeo && rh <= (os - 7);
  loop invariant 2 * (bc + 2) == yeo * (yeo + 9);
  loop invariant 0 <= rh && rh <= os - 7;
  loop invariant (w7 == 0) || (w7 == 1);
  loop invariant 0 <= rh && rh <= (os - 7);
  loop invariant bc == (-2 + ((yeo*(yeo + 1))/2) + 4*yeo);
  loop invariant 0 <= rh && rh <= os - 7 && rh <= yeo;
  loop assigns oqj, vc, w7, yeo, rh, bc, qlb;
*/
while (1) {
      if (!(yeo<os)) {
          break;
      }
      if (w7==0) {
          oqj += 2;
          vc -= 2;
          w7 = 1;
      }
      else {
          oqj -= 2;
          vc += 2;
          w7 = 0;
      }
      yeo = yeo + 1;
      if (rh+7<os) {
          rh += 1;
      }
      bc = bc + yeo;
      qlb = qlb + 3;
      bc += 4;
  }
}