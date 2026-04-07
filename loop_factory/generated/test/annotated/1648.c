int main1(){
  int i, dv, w4, k1co;
  i=1+24;
  dv=0;
  w4=0;
  k1co=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k1co + dv == 5;
  loop invariant w4 == dv*(11 - dv)/2;
  loop invariant k1co >= 0;
  loop invariant i == 25;
  loop invariant 0 <= dv <= i;
  loop assigns dv, k1co, w4;
*/
while (dv<i&&k1co>0) {
      w4 += k1co;
      dv += 1;
      k1co--;
  }
}