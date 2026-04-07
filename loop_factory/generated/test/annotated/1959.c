int main1(int d){
  int wkze, ui, go, x93l;
  wkze=(d%21)+17;
  ui=0;
  go=1;
  x93l=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ui == 0 || ui == wkze;
  loop invariant (ui == 0) ==> (go == 1 && x93l == \at(d, Pre));
  loop invariant wkze == (\at(d, Pre) % 21) + 17;
  loop invariant d == \at(d, Pre);
  loop invariant (ui == wkze) ==> ((go == 1 && x93l == \at(d, Pre)) || (go == \at(d, Pre) && x93l == \at(d, Pre) + \at(d, Pre)));
  loop invariant (ui == 0 && go == 1 && x93l == \at(d, Pre))
                   || (ui == wkze && go == \at(d, Pre) && x93l == 2 * \at(d, Pre));
  loop assigns ui, go, x93l;
*/
while (1) {
      if (!(ui < wkze)) {
          break;
      }
      go = (ui++, go * d);
      x93l += go;
      ui = wkze;
  }
}