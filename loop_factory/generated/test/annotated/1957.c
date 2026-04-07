int main1(){
  int jmx, h, w2, kw;
  jmx=10;
  h=0;
  w2=h;
  kw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= h;
  loop invariant h <= jmx;
  loop invariant (h >= jmx/2) ==> (w2 == (jmx - h) && kw == ((h - jmx/2)*jmx - h*(h+1)/2 + (jmx/2)*((jmx/2)+1)));
  loop invariant 0 <= w2;
  loop invariant 0 <= kw;
  loop invariant jmx == 10;
  loop invariant (2*h <= jmx) ==> (w2 == h && kw == (h*(h+1))/2);
  loop assigns h, w2, kw;
*/
while (1) {
      if (!(h < jmx)) {
          break;
      }
      w2 = w2 + (1 - 2*(2*h/jmx));
      h += 1;
      kw = kw + w2;
  }
}