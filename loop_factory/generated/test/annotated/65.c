int main1(){
  int mo, to;
  mo=1+6;
  to=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant to % 2 == 0;
  loop invariant 0 <= to;
  loop invariant to <= 6;
  loop invariant mo == 1 + 6;
  loop assigns to;
*/
while (to<mo) {
      to = (to+1)%6;
      to += 1;
  }
}