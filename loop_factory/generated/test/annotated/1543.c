int main1(){
  int p, l, q, hq, ot, bs, mna, vtp, h, ymze;
  p=1;
  l=-5;
  q=p;
  hq=0;
  ot=p;
  bs=p;
  mna=p;
  vtp=-6;
  h=6;
  ymze=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 1;
  loop invariant ot >= 1;
  loop invariant h >= 0;
  loop invariant bs >= 1;
  loop invariant mna >= 1;
  loop invariant hq >= 0;
  loop invariant 0 <= p - l <= 6;
  loop invariant l == -5;
  loop invariant ymze <= 1;
  loop assigns p, q, ot, h, ymze, bs, mna, hq;
*/
while (1) {
      if (!(l+1<=p)) {
          break;
      }
      if (!(!(l<p/2))) {
          q += 1;
      }
      else {
          q = q + hq;
      }
      if (l+6<=vtp+p) {
          ot += 1;
      }
      h = h + q;
      ymze = ymze+(l%2);
      bs = bs + q;
      mna = mna + q;
      hq++;
      ot = ot + hq;
      p = (l+1)-1;
      if (ymze+6<p) {
          ot += 1;
      }
  }
}