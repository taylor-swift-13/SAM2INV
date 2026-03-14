int main1(){
  int my5r, uy, z2, cc, h;
  my5r=1;
  uy=0;
  z2=0;
  cc=0;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == uy;
  loop invariant cc == uy % 6;
  loop invariant z2 == uy / 6;
  loop invariant 0 <= uy <= my5r;
  loop assigns h, cc, z2, uy;
*/
for (; uy<my5r; uy++) {
      h += 1;
      cc = cc + 1;
      if (cc>=6) {
          cc -= 6;
          z2++;
      }
  }
}