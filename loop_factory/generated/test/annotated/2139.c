int main1(){
  int h, emy, t3, h3, xs;
  h=1;
  emy=0;
  t3=0;
  h3=0;
  xs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= emy;
  loop invariant emy <= h;
  loop invariant h3 == emy * h;
  loop invariant t3 == h * emy * (emy + 1);
  loop invariant xs == ((emy*(emy - 1)/2) * (emy*(emy - 1)/2));
  loop invariant (4 * xs) == ((emy * (emy - 1)) * (emy * (emy - 1)));
  loop assigns xs, emy, h3, t3;
*/
while (1) {
      if (!(emy < h)) {
          break;
      }
      xs = xs + emy*emy*emy;
      emy++;
      h3 += h;
      t3 = t3+h3+h3;
  }
}