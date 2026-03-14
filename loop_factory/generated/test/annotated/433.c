int main1(int s){
  int bp9f, ljh, qr, oj;
  bp9f=72;
  ljh=2;
  qr=-1;
  oj=ljh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre) + (qr + 1) * bp9f;
  loop invariant 0 <= qr + 1;
  loop assigns qr, oj, s;
*/
while (qr<=bp9f-1) {
      qr += 1;
      oj = bp9f-qr;
      s = s + bp9f;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= \at(s, Pre) + 72;
  loop invariant bp9f >= 72;
  loop assigns bp9f, ljh, s;
*/
while (1) {
      if (!(bp9f<qr)) {
          break;
      }
      bp9f = bp9f + 1;
      ljh = qr-bp9f;
      s = s + bp9f;
  }
}