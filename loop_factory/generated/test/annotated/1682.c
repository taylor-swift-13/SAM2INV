int main1(){
  int rh, sj6, t6x;
  rh=1*3;
  sj6=0;
  t6x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t6x == 2 * (sj6 % 2);
  loop invariant rh == 3;
  loop invariant 0 <= sj6;
  loop invariant sj6 <= rh;
  loop assigns t6x, sj6;
*/
while (sj6 < rh) {
      t6x = 1 - t6x;
      sj6 += 1;
      t6x += 1;
  }
}