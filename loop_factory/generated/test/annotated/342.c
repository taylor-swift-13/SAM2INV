int main1(){
  int e, l4p, xo, yn0, w2;
  e=66;
  l4p=2;
  xo=0;
  yn0=-8;
  w2=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w2 == -1 + l4p * xo;
  loop invariant -8 <= yn0;
  loop invariant yn0 <= xo;
  loop invariant e == 66;
  loop invariant l4p == 2;
  loop invariant 0 <= xo <= e;
  loop assigns xo, w2, yn0;
*/
while (xo<e) {
      if (w2<e) {
          yn0 = xo;
      }
      xo = xo + 1;
      w2 += l4p;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e <= w2;
  loop invariant -8 <= yn0;
  loop invariant e >= 66;
  loop assigns xo, yn0, e;
*/
while (1) {
      xo = xo + yn0;
      yn0 = yn0 + w2;
      e += 1;
      if (e>=w2) {
          break;
      }
  }
}