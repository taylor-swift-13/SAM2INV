int main1(){
  int xrn, thu, q4, h, e7ve;
  xrn=(1%38)+18;
  thu=0;
  q4=2;
  h=6;
  e7ve=xrn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q4 == thu + 2;
  loop invariant h > 0;
  loop invariant e7ve - 2*thu == xrn;
  loop invariant 0 <= thu <= xrn;
  loop assigns e7ve, h, q4, thu;
*/
while (thu < xrn) {
      thu++;
      e7ve += 2;
      h += h;
      q4 = q4 + 1;
  }
}