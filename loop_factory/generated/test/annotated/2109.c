int main1(){
  int oz7, d, imo, s6, u;
  oz7=1;
  d=0;
  imo=1*4;
  s6=0;
  u=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oz7 == 1;
  loop invariant u == 0;
  loop invariant 0 <= d;
  loop invariant d <= oz7;
  loop invariant imo == 4 + (oz7 * d);
  loop invariant 2 * s6 == (u * d * (d - 1));
  loop assigns d, s6, imo;
*/
while (d < oz7) {
      s6 = (u * d)+(s6);
      d++;
      imo += oz7;
  }
}