int main1(){
  int u4, m1d, a5, gq;
  u4=(1%26)+9;
  m1d=0;
  a5=u4;
  gq=u4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u4 == m1d + a5;
  loop invariant gq == u4 + m1d*(m1d+1)/2;
  loop invariant 0 <= a5 <= u4;
  loop assigns a5, m1d, gq;
*/
while (m1d<u4&&a5>0) {
      a5--;
      m1d = (1)+(m1d);
      gq += m1d;
  }
}