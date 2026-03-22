int main1(int f){
  int fg3, ja77, tf, cw;
  fg3=f+25;
  ja77=0;
  tf=1;
  cw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(f, Pre) + ja77 * cw;
  loop invariant ja77 == 0;
  loop invariant fg3 == \at(f, Pre) + 25;
  loop invariant cw >= 0;
  loop invariant tf >= 1;
  loop assigns f, cw, tf;
*/
while (tf<=fg3) {
      f = f + ja77;
      cw += 1;
      tf = 2*tf;
  }
}