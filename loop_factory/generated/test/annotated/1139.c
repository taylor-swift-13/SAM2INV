int main1(){
  int jrq, i, gc, c, w66;
  jrq=(1%16)+7;
  i=0;
  gc=3;
  c=jrq;
  w66=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gc == 3;
  loop invariant jrq == 8;
  loop invariant i % 4 == 0;
  loop invariant i <= jrq;
  loop invariant (w66 - gc * (i / 4) == 12);
  loop assigns c, w66, i;
*/
while (i<jrq) {
      c = c + w66;
      w66 += gc;
      i += 4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gc <= i;
  loop invariant gc >= 3;
  loop invariant jrq >= 8;
  loop invariant i % 4 == 0;
  loop assigns jrq, gc;
*/
while (1) {
      jrq = jrq + jrq;
      jrq = jrq + w66;
      gc++;
      if (gc>=i) {
          break;
      }
  }
}