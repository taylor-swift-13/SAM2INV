int main1(){
  int evu, f0c, yhe, ci, e8;
  evu=1-10;
  f0c=0;
  yhe=0;
  ci=0;
  e8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ci == yhe*(yhe - 1) / 2;
  loop invariant e8 == f0c * yhe;
  loop invariant e8 == 0;
  loop invariant 0 <= yhe;
  loop assigns ci, e8, yhe;
*/
while (1) {
      if (!(yhe<=evu-1)) {
          break;
      }
      ci += yhe;
      e8 = e8 + f0c;
      yhe += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e8 == 0;
  loop invariant ((evu + 9) % 8) == 0;
  loop invariant evu >= -9;
  loop assigns evu;
*/
while (1) {
      if (!(evu<e8)) {
          break;
      }
      evu += 8;
  }
}