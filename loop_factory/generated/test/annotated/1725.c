int main1(){
  int i, oe, ye, h, j8g;
  i=(1%15)+17;
  oe=0;
  ye=oe;
  h=0;
  j8g=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j8g == 3 + 2*oe;
  loop invariant ye == oe;
  loop invariant h == (oe*(oe+2)) % 6;
  loop invariant 0 <= oe <= i;
  loop invariant i == 18;
  loop invariant (0 <= h && h <= 5);
  loop assigns h, oe, ye, j8g;
*/
while (1) {
      if (!(i > oe)) {
          break;
      }
      h = (h+j8g)%6;
      oe += 1;
      ye = ye + 1;
      j8g += 2;
  }
}