int main1(int h){
  int feq7, l8, qlq, gu, ouq, is;
  feq7=17;
  l8=feq7;
  qlq=48;
  gu=0;
  ouq=1;
  is=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qlq + gu == 48;
  loop invariant l8 <= feq7;
  loop invariant 0 <= l8;
  loop invariant 0 <= qlq;
  loop invariant 0 <= gu;
  loop invariant 0 <= is;
  loop invariant ouq >= 1;
  loop assigns qlq, l8, gu, ouq, is;
*/
while (qlq>0&&l8<feq7) {
      if (qlq<=ouq) {
          is = qlq;
      }
      else {
          is = ouq;
      }
      l8 += 1;
      gu += is;
      ouq += 1;
      qlq -= is;
  }
}