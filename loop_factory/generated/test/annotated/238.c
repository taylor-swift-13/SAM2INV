int main1(){
  int q5, ja0;
  q5=24;
  ja0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q5 == 24;
  loop invariant ja0 <= 2*q5 + 1;
  loop invariant (ja0 == 0) || (ja0 % 2 == 1);
  loop assigns ja0;
*/
while (ja0<=q5) {
      ja0 = 2*ja0;
      ja0 += 1;
  }
}