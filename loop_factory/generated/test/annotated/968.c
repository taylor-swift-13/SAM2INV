int main1(){
  int lzm, qf1, ou;
  lzm=(1%20)+5;
  qf1=(1%20)+5;
  ou=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ou >= 0;
  loop invariant lzm == ou;
  loop invariant lzm <= 6;
  loop invariant qf1 == 6;
  loop assigns lzm, qf1, ou;
*/
while (lzm>0) {
      if (qf1>0) {
          if (ou>0) {
              lzm--;
              qf1--;
              ou--;
          }
      }
      qf1 = qf1 + 1;
  }
}