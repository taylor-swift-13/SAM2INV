int main1(int x){
  int c6m, hh, oz, osfx, v;
  c6m=42;
  hh=0;
  oz=0;
  osfx=0;
  v=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(x, Pre) + 3 * hh;
  loop invariant oz == 3 * hh;
  loop invariant osfx == hh;
  loop invariant 0 <= hh;
  loop invariant hh <= c6m;
  loop invariant v - oz == \at(x, Pre);
  loop assigns v, hh, oz, osfx;
*/
while (hh < c6m) {
      v = v + 3;
      hh++;
      oz = oz + 3;
      osfx++;
  }
}