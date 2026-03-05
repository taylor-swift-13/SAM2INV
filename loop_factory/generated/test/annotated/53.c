int main1(){
  int zb, yru6;
  zb=1;
  yru6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zb == 1;
  loop invariant 0 <= yru6;
  loop invariant zb - yru6 >= 0;
  loop assigns yru6;
*/
while (yru6<zb) {
      yru6 = 2*yru6;
      yru6++;
  }
}