int main1(int m){
  int st, ix, g3, j30n, e7;
  st=75;
  ix=0;
  g3=0;
  j30n=st;
  e7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 8*e7 == g3*(g3+4);
  loop invariant ((g3 != 0) ==> (j30n == g3 - 4));
  loop invariant (st == 75);
  loop assigns j30n, g3, e7;
*/
while (1) {
      if (!(g3<=st-1)) {
          break;
      }
      j30n = g3;
      g3 += 4;
      e7 += g3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ix == 0);
  loop invariant (st == 75);
  loop assigns e7, g3, j30n;
*/
while (1) {
      if (!(e7<ix)) {
          break;
      }
      e7 = e7 + 1;
      g3 = g3 + m;
      j30n += g3;
  }
}