int main1(int d){
  int bn0, rx, r4, y0;
  bn0=53;
  rx=0;
  r4=rx;
  y0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rx;
  loop invariant rx <= bn0;
  loop invariant y0 == d * rx;
  loop invariant r4 == d * rx * (rx + 1) / 2;
  loop assigns rx, y0, r4;
*/
while (1) {
      if (!(rx < bn0)) {
          break;
      }
      rx = rx + 1;
      y0 += d;
      r4 = r4 + y0;
  }
}