int main1(){
  int w5m, gw, s2g, j2a;
  w5m=(1%18)+17;
  gw=-1;
  s2g=0;
  j2a=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= s2g;
  loop invariant s2g <= 8;
  loop invariant j2a * j2a == 1;
  loop invariant gw <= w5m;
  loop invariant w5m == 18;
  loop invariant gw >= -1;
  loop invariant (gw + s2g + 1) >= 0;
  loop invariant ((gw + s2g + 1) % 2) == 0;
  loop invariant gw - s2g >= -1;
  loop assigns gw, s2g, j2a;
*/
while (gw<w5m) {
      if (!(s2g<8)) {
          j2a = -1;
      }
      if (s2g<=0) {
          j2a = 1;
      }
      gw = gw + 1;
      s2g = s2g + j2a;
  }
/*@
  assert !(gw<w5m) &&
         (0 <= s2g);
*/

}