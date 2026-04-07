int main1(int s){
  int m96j, w0, qs, cl, lug;
  m96j=s;
  w0=0;
  qs=5;
  cl=w0;
  lug=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m96j - w0 == \at(s, Pre);
  loop invariant lug == w0;
  loop invariant qs == 5;
  loop invariant m96j - w0 == s;
  loop invariant w0 >= 0;
  loop invariant cl == ((-w0) * w0 + 3 * w0) / 2;
  loop invariant lug <= 0;
  loop invariant m96j <= \at(s, Pre);
  loop assigns m96j, w0, qs, cl, lug;
*/
while (w0 > 0 && m96j > 0) {
      w0 = w0 = w0 - 1, m96j = m96j - 1, qs = qs - 1, cl = cl - 1, lug = lug - 1;
      qs = qs + 1;
      cl = cl + w0;
  }
}