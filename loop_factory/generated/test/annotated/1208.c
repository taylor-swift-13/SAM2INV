int main1(){
  int o, tqk, c6, b, g;
  o=1;
  tqk=o+2;
  c6=0;
  b=0;
  g=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b <= o;
  loop invariant c6 == b;
  loop invariant o == 1;
  loop invariant tqk == o + 2;
  loop invariant 0 <= b;
  loop invariant g == 2 + (o + tqk) * b;
  loop assigns g, b, c6;
*/
while (1) {
      if (!(b<o)) {
          break;
      }
      g = g + o;
      b += 1;
      c6 = c6 + 1;
      g += tqk;
  }
}