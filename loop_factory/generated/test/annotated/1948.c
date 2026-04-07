int main1(){
  int e, qlb, xgqp;
  e=1*5;
  qlb=0;
  xgqp=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qlb;
  loop invariant qlb <= e;
  loop invariant xgqp == 20 + (qlb * (qlb + 3)) / 2;
  loop invariant e == 5;
  loop assigns qlb, xgqp;
*/
while (qlb < e) {
      qlb++;
      xgqp = xgqp + qlb;
      xgqp++;
  }
}