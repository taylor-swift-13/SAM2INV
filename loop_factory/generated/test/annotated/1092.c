int main1(){
  int so, ba7, h, r, o, rny, b3;
  so=1*3;
  ba7=1;
  h=0;
  r=(1%28)+10;
  o=so;
  rny=ba7;
  b3=so;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rny - ba7 * h == ba7;
  loop invariant r >= 0;
  loop invariant h >= 0;
  loop invariant ba7 == 1;
  loop invariant r + (h * (h - 1)) / 2 == 11;
  loop invariant o > 0;
  loop invariant b3 > 0;
  loop assigns b3, r, h, o, rny;
*/
while (r>h) {
      r -= h;
      h += 1;
      o = o*2;
      rny += ba7;
      b3 = b3+so-ba7;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ba7 >= 1;
  loop invariant r >= 0;
  loop invariant h >= 0;
  loop invariant so > 0;
  loop invariant (r - h) % 2 == 0;
  loop assigns ba7, h, so, r;
*/
while (1) {
      if (!(r>=1)) {
          break;
      }
      ba7 = ba7+1*1;
      h = h+1*1;
      so = so+1*1;
      r = (r)+(-(1));
      so = so*2;
  }
}