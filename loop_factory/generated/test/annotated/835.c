int main1(){
  int zh, ur, ek, q3, xm, a5x;
  zh=(1%31)+6;
  ur=zh;
  ek=zh;
  q3=-6;
  xm=(1%6)+2;
  a5x=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q3 <= zh;
  loop invariant ur >= 0;
  loop invariant ek >= 0;
  loop invariant xm == 3;
  loop invariant a5x - zh*q3 == zh*6 - 5;
  loop invariant zh == 7;
  loop assigns q3, a5x, ur, ek;
*/
while (1) {
      if (q3>=zh) {
          break;
      }
      q3 += 1;
      a5x += zh;
      ur = ur*xm+1;
      ek = ek*xm;
  }
}