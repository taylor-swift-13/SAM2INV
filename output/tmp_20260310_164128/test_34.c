int main1(int p){
  int y8y, ui, kimp, s, y;
  y8y=p;
  ui=y8y;
  kimp=y8y;
  s=0;
  y=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y8y == \at(p, Pre);
  loop invariant (
       (ui == \at(p, Pre) &&
        kimp == \at(p, Pre) &&
        s == 0 &&
        p == \at(p, Pre) &&
        y == 6
       )
       ||
       (ui == 3 &&
        kimp == 2 * \at(p, Pre) &&
        s == \at(p, Pre) * \at(p, Pre) &&
        p == \at(p, Pre) + 2 &&
        y == 6 + (\at(p, Pre) * \at(p, Pre))
       )
     );
  loop invariant (ui == \at(p, Pre) ==> s == 0 && p == \at(p, Pre) && kimp == \at(p, Pre) && y == 6 && y8y == \at(p, Pre));
  loop invariant ((ui == \at(p,Pre) && s == 0 && kimp == \at(p,Pre) && p == \at(p,Pre) && y == 6) || ui == 3);
  loop invariant kimp >= \at(p,Pre);
  loop invariant s >= 0;
  loop invariant p >= \at(p,Pre);
  loop invariant y == 6 + s;
  loop assigns s, kimp, p, y, ui;
*/
while (ui>3) {
      s = s+kimp*ui;
      kimp += ui;
      p += 2;
      y = y + s;
      ui = 3;
  }
/*@
  assert (ui <= 3) &&
         (kimp >= \at(p, Pre)) &&
         (s >= 0) &&
         (p >= \at(p, Pre)) &&
         (y == 6 + s);
*/
}
