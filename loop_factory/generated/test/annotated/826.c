int main1(){
  int zh, bt, m41, mui, j1, c4;
  zh=1+14;
  bt=zh+7;
  m41=bt;
  mui=-2;
  j1=bt;
  c4=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zh == 15;
  loop invariant c4 >= 0;
  loop invariant mui <= 0;
  loop invariant m41 >= 2;
  loop invariant j1 >= 22;
  loop invariant (m41 % 2) == 0;
  loop assigns mui, m41, j1, c4;
*/
while (1) {
      if (!(j1<zh)) {
          break;
      }
      mui = mui*c4;
      m41 = m41*c4+2;
      j1 += 1;
      c4 = c4 + mui;
      c4 = c4*c4;
  }
}