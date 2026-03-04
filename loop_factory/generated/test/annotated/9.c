int main1(){
  int g24h, fx;
  g24h=0;
  fx=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g24h == 0;
  loop invariant fx >= 0;
  loop invariant fx <= (1 % 20) + 5;
  loop invariant fx <= 6;
  loop assigns fx;
*/
while (fx>0) {
      fx--;
      fx = fx + g24h;
  }
}