int main1(){
  int ws, t2;
  ws=1-6;
  t2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t2 % 2 == 0;
  loop invariant t2 >= 0;
  loop invariant ws == 1 - 6;
  loop assigns t2;
*/
for (; t2+2<=ws; t2 += 2) {
  }
}