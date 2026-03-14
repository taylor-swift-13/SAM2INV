int main1(){
  int asqo, qefq, bgt, ap, q6t;
  asqo=1+24;
  qefq=0;
  bgt=qefq;
  ap=0;
  q6t=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant asqo == 25;
  loop invariant ap == asqo - 25;
  loop invariant ((qefq == 0 && ap == 0 && bgt == 0) || (qefq == asqo && ap == bgt * asqo));
  loop assigns ap, bgt, qefq;
*/
while (qefq<asqo) {
      ap = ap+bgt*qefq;
      bgt = bgt + qefq;
      qefq = asqo;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant asqo >= bgt;
  loop invariant qefq >= 25;
  loop invariant ap == asqo - 25;
  loop invariant qefq == 2*asqo - 25;
  loop assigns ap, asqo, qefq;
*/
while (asqo<bgt) {
      asqo++;
      qefq = qefq + q6t;
      ap += 1;
  }
}