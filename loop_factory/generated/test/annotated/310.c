int main1(){
  int zztm, d, vl2;
  zztm=(1%30)+17;
  d=zztm;
  vl2=zztm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zztm == (1%30)+17;
  loop invariant vl2 >= zztm;
  loop invariant vl2 % 2 == 0;
  loop invariant d == zztm;
  loop assigns vl2;
*/
while (d>1) {
      if (d<zztm/2) {
          vl2 += vl2;
      }
      else {
          vl2 = vl2 + 1;
      }
      vl2 = vl2 + 5;
      vl2 += vl2;
  }
}