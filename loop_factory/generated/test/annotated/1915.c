int main1(){
  int r, e, mw, g, ilb, mm, ij, i;
  r=1*4;
  e=3;
  mw=18;
  g=14;
  ilb=0;
  mm=e;
  ij=e;
  i=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mw + g == 32;
  loop invariant ij == 3;
  loop invariant i == 3;
  loop invariant ilb == (e - 3) % 2;
  loop invariant 3 <= e;
  loop invariant e <= r;
  loop invariant mm >= 3 + (e - 3) * 6;
  loop invariant mm <= 3 + (e - 3) * 7;
  loop invariant r == 4;
  loop assigns mw, g, ilb, e, i, mm;
*/
while (e<r) {
      if (ilb==0) {
          mw = mw + 3;
          g = g - 3;
          ilb = 1;
      }
      else {
          mw = mw - 3;
          g = g + 3;
          ilb = 0;
      }
      e += 1;
      if (i+2<r) {
          i = i - g;
      }
      mm = mm + ilb;
      mm = mm+ij+i;
  }
}