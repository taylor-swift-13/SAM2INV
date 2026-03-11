int main1(int a){
  int y, h, v;

  y=(a%7)+18;
  h=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant y == (a % 7) + 18;
  loop invariant h % 5 == 0;
  loop invariant h >= 0;
  loop invariant v <= -5;
  loop invariant y == ((\at(a, Pre)) % 7) + 18;
  loop invariant h <= y + 4;
  loop invariant v % 5 == 0;
  loop invariant y == (\at(a, Pre) % 7) + 18;
  loop invariant 0 <= h;

  loop invariant v < 0;
  loop invariant y == \at(a, Pre) % 7 + 18;
  loop assigns h, v;
*/
while (h<y) {
      v = v+v;
      h = h+5;
  }

}
