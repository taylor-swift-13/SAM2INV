int main1(int x,int m){
  int r4, z4, a, tpiy, f, q7;
  r4=65;
  z4=r4;
  a=34;
  tpiy=0;
  f=1;
  q7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tpiy == 34 - a;
  loop invariant 0 <= a;
  loop invariant z4 <= r4;
  loop invariant f >= 1;
  loop invariant tpiy >= 0;
  loop invariant q7 >= 0;
  loop invariant z4 - r4 == f - 1;
  loop assigns a, f, z4, tpiy, q7;
*/
while (1) {
      if (!(a>0&&z4<r4)) {
          break;
      }
      if (a<=f) {
          q7 = a;
      }
      else {
          q7 = f;
      }
      f = f + 1;
      z4 = z4 + 1;
      tpiy += q7;
      a -= q7;
  }
}