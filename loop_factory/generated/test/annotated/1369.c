int main1(){
  int ehz, yp, gqu;
  ehz=1+5;
  yp=0;
  gqu=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gqu % 8 == 0;
  loop invariant 0 <= yp;
  loop invariant yp <= ehz;
  loop invariant gqu >= 8;
  loop invariant ehz == 6;
  loop assigns gqu, yp;
*/
while (1) {
      gqu = gqu*2;
      yp += 1;
      if (yp>=ehz) {
          break;
      }
  }
}