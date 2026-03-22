int main1(){
  int em, mm, tc, ogr, ogmt;
  em=52;
  mm=em;
  tc=0;
  ogr=0;
  ogmt=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ogr == tc;
  loop invariant ogmt == 4 + tc * em;
  loop invariant em == 52;
  loop invariant mm == 52;
  loop invariant 0 <= tc;
  loop invariant tc <= em;
  loop assigns ogmt, tc, ogr;
*/
while (1) {
      if (!(ogr<em)) {
          break;
      }
      ogmt = (ogmt+em)+(-(mm));
      tc += 1;
      ogr++;
      ogmt += mm;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant em >= 0;
  loop invariant mm >= 0;
  loop invariant tc >= 0;
  loop invariant ogr == tc;
  loop invariant ogmt >= ogr;
  loop assigns em, mm, ogmt;
*/
while (1) {
      em += mm;
      mm = mm+(em%2);
      mm = mm + tc;
      ogmt++;
      if (ogmt>=ogr) {
          break;
      }
  }
}