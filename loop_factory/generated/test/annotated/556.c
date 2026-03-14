int main1(){
  int tw, i, louv, dw4;
  tw=46;
  i=1;
  louv=0;
  dw4=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant louv >= 0 &&
                    i >= 1 &&
                    i <= 2*tw - 1 &&
                    dw4 >= 2 &&
                    tw == 46;
  loop invariant louv >= 0;
  loop invariant i >= 1;
  loop invariant dw4 == 2*i*(1 + tw) - 2*tw;
  loop assigns i, louv, dw4;
*/
while (1) {
      if (!(i<tw)) {
          break;
      }
      louv++;
      dw4 = dw4 + tw;
      i = 2*i;
      dw4 = dw4 + dw4;
  }
}