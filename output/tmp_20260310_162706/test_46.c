int main1(int w,int n){
  int o9, pjr, ff, sw, byc;
  o9=w;
  pjr=o9;
  ff=0;
  sw=2;
  byc=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o9 == \at(w,Pre);
  loop invariant pjr == o9;
  loop invariant byc == ff + 2;
  loop invariant sw == ff + 2;
  loop invariant ff >= 0;
  loop invariant ff % 4 == 0;
  loop invariant w == \at(w,Pre) + (ff/4) * (\at(w,Pre) + 4);
  loop assigns ff, w, byc, sw;
*/
while (ff<o9) {
      ff += 4;
      w += pjr;
      byc += 4;
      sw += 4;
      w += 4;
  }
/*@
  assert !(ff<o9) &&
         (o9 == \at(w,Pre));
*/

}