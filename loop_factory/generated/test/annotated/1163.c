int main1(){
  int l, c9, j2c, zu, i, h;
  l=1;
  c9=0;
  j2c=0;
  zu=1;
  i=1;
  h=c9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zu == (j2c + 1) * (j2c + 1);
  loop invariant i == 1 + 2 * j2c;
  loop invariant h == ((j2c + 1) * (j2c + 2) * (2 * j2c + 3)) / 3 - 2;
  loop invariant 0 <= j2c <= 1;
  loop invariant l == 1;
  loop assigns j2c, i, zu, h;
*/
while (1) {
      if (!(zu<=l)) {
          break;
      }
      j2c = j2c + 1;
      i += 2;
      zu = zu + i;
      h = h+zu+zu;
  }
}