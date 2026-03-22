int main1(){
  int tg, y7, eo, qe6, y, su, lv8i;
  tg=48;
  y7=tg;
  eo=0;
  qe6=1;
  y=6;
  su=0;
  lv8i=y7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 6 + 2*su;
  loop invariant lv8i == 48 + su*su + 7*su;
  loop invariant qe6 == su*su + 5*su + 1;
  loop invariant eo == (su*(su-1)*(2*su-1))/6 + (5*su*(su-1))/2 + su;
  loop invariant 0 <= su <= tg+1;
  loop invariant eo == (su*(su*su + 6*su - 4))/3;
  loop invariant lv8i - qe6 - 2*su == 47;
  loop invariant qe6 >= 1;
  loop assigns eo, lv8i, qe6, su, y;
*/
while (su<=tg) {
      su++;
      eo += qe6;
      qe6 = qe6 + y;
      y += 2;
      lv8i = lv8i + y;
  }
}