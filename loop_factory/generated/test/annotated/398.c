int main1(){
  int n9c, xm, q, mh, a;
  n9c=1;
  xm=n9c;
  q=31;
  mh=1;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n9c == 1;
  loop invariant mh == a + 1;
  loop invariant q >= 0;
  loop invariant a == xm - 1;
  loop invariant q + a*(a+1)/2 == 31;
  loop invariant xm >= 1;
  loop assigns a, mh, q, xm;
*/
while (q>0&&mh<=n9c) {
      if (q>mh) {
          q = q - mh;
      }
      else {
          q = 0;
      }
      mh = mh + 1;
      xm++;
      a++;
  }
}