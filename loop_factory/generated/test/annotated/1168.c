int main1(){
  int hq, qzp, gi, en, x;
  hq=1-10;
  qzp=0;
  gi=1;
  en=1;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant en == 2*qzp + 1;
  loop invariant gi == (qzp + 1) * (qzp + 1);
  loop invariant x == qzp * (qzp + 1) / 2;
  loop invariant qzp >= 0;
  loop assigns qzp, en, x, gi;
*/
while (gi<=hq) {
      qzp += 1;
      en += 2;
      x = x + qzp;
      gi = gi + en;
  }
}