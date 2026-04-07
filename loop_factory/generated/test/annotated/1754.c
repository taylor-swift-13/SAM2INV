int main1(){
  int h6g, swst, n, xl4, xc, va3;
  h6g=(1%29)+10;
  swst=0;
  n=swst;
  xl4=h6g;
  xc=swst;
  va3=swst;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xl4 == h6g;
  loop invariant n == h6g * swst;
  loop invariant va3 == 2 * h6g * swst;
  loop invariant swst <= h6g;
  loop invariant n == swst*h6g + xc*swst*(swst-1)/2;
  loop invariant xl4 == h6g + swst*xc;
  loop invariant va3 == 2*swst*h6g + xc*swst*(swst-1);
  loop invariant (va3 == 2 * swst * h6g);
  loop assigns n, xl4, swst, va3;
*/
while (1) {
      if (!(swst < h6g)) {
          break;
      }
      n += xl4;
      xl4 = (xc)+(xl4);
      swst = swst + 1;
      va3 = va3+xl4+xl4;
  }
}