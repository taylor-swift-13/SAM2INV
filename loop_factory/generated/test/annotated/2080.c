int main1(){
  int go1, tder, q, ep;
  go1=1;
  tder=0;
  q=tder;
  ep=go1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == tder;
  loop invariant (tder == 0 ==> ep == 1) && (tder >= 1 ==> ep == 0);
  loop invariant (0 <= tder && tder <= go1);
  loop assigns q, ep, tder;
*/
while (tder < go1) {
      q += 1;
      ep = ep - ep/(tder+1);
      tder += 1;
  }
}