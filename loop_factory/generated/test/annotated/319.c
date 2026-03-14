int main1(){
  int lfw, zy, nr, obar;
  lfw=1;
  zy=1;
  nr=0;
  obar=lfw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nr <= lfw;
  loop invariant zy - nr == 1;
  loop assigns nr, zy;
*/
while (1) {
      if (!(nr<lfw)) {
          break;
      }
      zy = zy + 1;
      nr += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nr == obar;
  loop invariant lfw - obar >= 0;
  loop assigns nr, obar;
*/
while (obar<=lfw-1) {
      nr += 1;
      obar = obar + 1;
  }
}