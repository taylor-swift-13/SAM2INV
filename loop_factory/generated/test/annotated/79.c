int main1(){
  int xjf7, q1, q7;
  xjf7=1;
  q1=xjf7;
  q7=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xjf7 == 1;
  loop invariant q7 == 5*q1 + 4;
  loop invariant q7 >= 9;
  loop assigns q1, q7;
*/
while (q7>0&&q7>0) {
      if (q1%2==0) {
          q7--;
      }
      else {
          q7--;
      }
      q1 = q1 + 1;
      q7 += 6;
  }
}