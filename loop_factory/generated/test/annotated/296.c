int main1(){
  int drf, b, g, h;
  drf=15;
  b=0;
  g=0;
  h=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (h == -2) ==> (g == 0);
  loop invariant g % 4 == 0;
  loop invariant (h == -2) || (h == 0);
  loop invariant drf == 15;
  loop assigns g, h;
*/
while (g<drf) {
      h = drf-g;
      h -= h;
      g += 4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (h == 0);
  loop invariant (b >= 0);
  loop invariant b <= h;
  loop invariant drf == 15;
  loop invariant (g >= 0);
  loop assigns g, b;
*/
for (; b<=h-1; b += 1) {
      g = g + 5;
      if (b+3<=h+h) {
          g++;
      }
  }
}