int main1(int y){
  int gh, cj, ltx;
  gh=y;
  cj=0;
  ltx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ltx;
  loop invariant ltx <= 1;
  loop invariant cj >= 0;
  loop invariant gh == y;
  loop invariant ((ltx == 0) || (ltx == 1)) && ((ltx == 0) || (ltx <= gh)) && (0 <= cj);
  loop invariant (cj == 0) ==> (ltx == 0);
  loop invariant (ltx == 0) ==> (cj == 0);
  loop invariant y == \at(y, Pre);
  loop assigns cj, ltx;
*/
for (; ltx>0&&ltx<=gh; cj++) {
      if (ltx>ltx) {
          ltx -= ltx;
      }
      else {
          ltx = 0;
      }
      ltx += 1;
  }
}