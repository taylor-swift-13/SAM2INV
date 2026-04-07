int main1(int y){
  int v0u, j, i5o, hypb, w, hkb, ek, m, r8;
  v0u=39;
  j=0;
  i5o=0;
  hypb=0;
  w=0;
  hkb=0;
  ek=0;
  m=0;
  r8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == ek;
  loop invariant i5o == ek % 4;
  loop invariant m == 7 * ek;
  loop invariant w == 6 * (ek / 4) + ((ek % 4) * ((ek % 4) + 1)) / 2;
  loop invariant y == \at(y, Pre) + w;
  loop invariant 0 <= ek <= v0u;
  loop invariant 0 <= i5o < 4;
  loop invariant 0 <= hypb < 5;
  loop invariant (0 <= hkb && hkb < 7);
  loop invariant (0 <= r8);
  loop assigns i5o, j, hypb, w, hkb, ek, m, r8, y;
*/
while (j < v0u) {
      i5o = (i5o + 1) % 4;
      j++;
      hypb = (hypb + 3) % 5;
      w = w + i5o;
      hkb = (hkb + w) % 7;
      ek++;
      if (y != 0) {
          r8 = j % y;
      }
      else {
          r8 = 0;
      }
      if (i5o<hypb+5) {
          m += 6;
      }
      y = y + i5o;
      m = (1)+(m);
  }
}