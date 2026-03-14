int main1(){
  int py, tpv, inz;
  py=1+7;
  tpv=0;
  inz=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant py == 8;
  loop invariant tpv % 4 == 0;
  loop invariant 0 <= tpv <= py;
  loop invariant (inz % 2) == 0;
  loop assigns inz, tpv;
*/
while (tpv+4<=py) {
      if (tpv+3<=py+py) {
          inz = inz + inz;
      }
      tpv += 4;
  }
}