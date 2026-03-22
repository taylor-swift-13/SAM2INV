int main1(){
  int hs, y17, emw, y5;
  hs=(1%38)+11;
  y17=hs;
  emw=hs;
  y5=y17;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant emw >= y5;
  loop invariant ((y17 == 12 && y5 == 12 && emw == 12) ||
                    (y17 == 3  && y5 == 13 && emw == 169));
  loop invariant y5 >= 12;
  loop invariant (y17 == 12) || (y17 == 3);
  loop invariant hs == (1%38) + 11;
  loop assigns emw, y5, y17;
*/
while (1) {
      if (!(y17>3)) {
          break;
      }
      y5 = y5 + 1;
      emw = y5*y5;
      y17 = 3;
  }
}