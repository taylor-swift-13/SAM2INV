int main1(){
  int ep, whwd, mb, m, yr, q, p, tm;
  ep=1*2;
  whwd=ep;
  mb=whwd;
  m=whwd;
  yr=ep;
  q=-4;
  p=5;
  tm=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ep == 2;
  loop invariant tm == 2;
  loop invariant mb >= 1;
  loop invariant mb <= whwd;
  loop invariant m <= whwd;
  loop invariant yr <= whwd;
  loop invariant mb + m == whwd + 2;
  loop invariant mb + m + yr <= 3*whwd;
  loop invariant yr >= 2;
  loop assigns mb, m, yr, q, p, whwd;
*/
while (1) {
      if (!(whwd-2>=0)) {
          break;
      }
      if (whwd%3==1) {
          mb = mb + 1;
      }
      else {
          m++;
      }
      if (whwd%3==2) {
          yr++;
      }
      else {
      }
      q = (ep)+(q);
      q = q+p+tm;
      p = p + q;
      if ((whwd%7)==0) {
          p += whwd;
      }
      q = m;
      q += whwd;
      p = q-p;
      whwd++;
  }
}