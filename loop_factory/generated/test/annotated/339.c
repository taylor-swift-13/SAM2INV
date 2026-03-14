int main1(){
  int mra, s, pw, aq, uirq;
  mra=0;
  s=(1%18)+5;
  pw=(1%15)+3;
  aq=s;
  uirq=mra;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mra == 0;
  loop invariant s >= 0;
  loop invariant pw == s - 2;
  loop invariant s <= 6;
  loop invariant aq == 6 + ((6 - s) * (s + 5)) / 2;
  loop assigns s, pw, aq;
*/
while (1) {
      if (!(s!=0)) {
          break;
      }
      s -= 1;
      pw--;
      aq = aq + s;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mra == 0;
  loop invariant s == uirq;
  loop invariant aq == 21 + uirq*(uirq + 1)/2;
  loop invariant uirq >= 0;
  loop invariant uirq <= mra;
  loop assigns aq, s, uirq;
*/
while (uirq<=mra-1) {
      s++;
      uirq += 1;
      aq = aq + uirq;
  }
}