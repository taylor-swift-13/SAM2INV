int main1(){
  int p6, c, f, d5cs, xph;
  p6=58;
  c=0;
  f=1;
  d5cs=0;
  xph=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d5cs == (f - 1) * f * (2 * f - 1) / 6;
  loop invariant xph == (f - 1) * p6 - 1;
  loop invariant 1 <= f <= p6 + 1;
  loop assigns d5cs, xph, f;
*/
while (f<=p6) {
      d5cs = d5cs+f*f;
      xph += p6;
      f = f + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c;
  loop invariant c <= d5cs;
  loop assigns c;
*/
while (1) {
      c = c + 1;
      if (c>=d5cs) {
          break;
      }
  }
/*@
  assert (d5cs == (f - 1) * f * (2 * f - 1) / 6);
*/

}