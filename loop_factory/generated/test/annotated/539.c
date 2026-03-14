int main1(){
  int ms, k, yd, hw, yw, e;
  ms=1;
  k=0;
  yd=0;
  hw=0;
  yw=6;
  e=ms;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hw == yd*yw + yd*(yd+1)/2;
  loop invariant 0 <= yd;
  loop invariant yd <= ms;
  loop invariant 0 <= yw;
  loop invariant 0 <= hw;
  loop invariant e == 1 + k * yd;
  loop invariant k == 0;
  loop invariant ms == 1;
  loop invariant yw == 6 - yd;
  loop assigns hw, yd, e, yw;
*/
while (1) {
      if (!(yd<ms&&yw>0)) {
          break;
      }
      hw += yw;
      yd += 1;
      e = e + k;
      yw--;
  }
}