int main1(){
  int qr, i4i, d5, isz;
  qr=(1%39)+12;
  i4i=0;
  d5=qr;
  isz=qr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant isz == qr;
  loop invariant 0 <= i4i;
  loop invariant i4i <= qr;
  loop invariant d5 >= isz;
  loop invariant d5 >= qr;
  loop invariant qr == 13;
  loop invariant (d5 - 13) % 17 == 0;
  loop assigns d5, i4i;
*/
while (i4i < qr) {
      d5 += isz;
      i4i = i4i + (qr - i4i + 1)/2;
      d5 += 4;
  }
}