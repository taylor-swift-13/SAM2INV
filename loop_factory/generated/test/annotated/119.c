int main1(){
  int na, p2, kl;
  na=1+15;
  p2=0;
  kl=na;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= p2 && p2 <= na);
  loop invariant kl >= 2;
  loop invariant ((p2 == 0) ==> (kl == na)) && ((p2 != 0) ==> (kl == na - p2 + 2));
  loop assigns kl, p2;
*/
while (p2<=na-1) {
      kl = na-p2;
      kl += 1;
      p2 = p2 + 1;
  }
}