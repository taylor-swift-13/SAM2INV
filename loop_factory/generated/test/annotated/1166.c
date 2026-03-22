int main1(){
  int ct, tx, cvd, djr, la;
  ct=1+3;
  tx=0;
  cvd=(1%28)+10;
  djr=ct;
  la=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant la == 8 + 3*tx;
  loop invariant 4 <= djr;
  loop invariant djr <= 4 + 7*tx;
  loop invariant tx >= 0;
  loop invariant ct == 4;
  loop invariant cvd + (tx*(tx-1))/2 == 11;
  loop assigns cvd, tx, la, djr;
*/
while (cvd>tx) {
      cvd -= tx;
      tx += 1;
      la = la + 3;
      djr = djr+(tx%8);
  }
}