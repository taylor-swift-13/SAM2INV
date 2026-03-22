int main1(){
  int fiq, ep, avc, l;
  fiq=1;
  ep=fiq;
  avc=ep;
  l=ep;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant avc == l * l;
  loop invariant l >= 1;
  loop invariant ep >= 0;
  loop invariant ep <= 1;
  loop invariant fiq == 1;
  loop assigns l, avc, ep;
*/
while (ep>=1) {
      l = l + 1;
      avc = l*l;
      ep = 0;
  }
}