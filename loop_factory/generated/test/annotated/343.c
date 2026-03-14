int main1(){
  int v5j5, qfm, qet, s, v0, ch;
  v5j5=1*4;
  qfm=0;
  qet=-4;
  s=qfm;
  v0=qfm;
  ch=v5j5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (qet - s == -4) || (qet - s == 1);
  loop invariant ch == v5j5 + (qet + 4) * qfm;
  loop invariant ch == 4;
  loop invariant qfm == 0;
  loop invariant -4 <= qet <= v5j5;
  loop invariant s <= v5j5 - 1;
  loop assigns s, ch, qet;
*/
while (qet+1<=v5j5) {
      s = qet;
      ch += qfm;
      qet = qet + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v0 >= 0;
  loop invariant qet <= v5j5;
  loop invariant s <= v5j5 - 1;
  loop assigns v0, qet;
*/
while (1) {
      if (!(qet<v5j5)) {
          break;
      }
      v0++;
      qet = qet + 1;
      if ((s%4)==0) {
          v0 += v0;
      }
  }
}