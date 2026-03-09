int main1(){
  int vu, acc, p6, aqq, ks;
  vu=(1%8)+5;
  acc=0;
  p6=0;
  aqq=0;
  ks=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (p6 + ks == 7);
  loop invariant aqq == acc * p6 + 7 * p6 - ((p6 * (p6 - 1)) / 2);
  loop invariant 0 <= p6;
  loop invariant p6 <= vu;
  loop invariant aqq == 7*p6 - (p6*(p6 - 1))/2;
  loop assigns p6, ks, aqq;
*/
while (p6<vu&&ks>0) {
      p6++;
      aqq += ks;
      ks--;
      aqq = aqq + acc;
  }
}