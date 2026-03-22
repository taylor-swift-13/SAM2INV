int main1(int n){
  int cm9h, wd, u8e, njc;
  cm9h=n+24;
  wd=cm9h;
  u8e=-1;
  njc=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (njc == 2) ==> (u8e == -1);
  loop invariant (njc > 2) ==> (u8e == -1 + njc*njc*njc*njc*njc);
  loop invariant cm9h == \at(n, Pre) + 24;
  loop invariant ((njc == 2) ==> (u8e == -1 && wd == cm9h)) &&
                   ((njc == 3) ==> (u8e == 242 && wd == 3));
  loop invariant njc >= 2;
  loop invariant u8e == (njc * njc * (njc + 1) * (njc + 1) * (2 * njc * njc + 2 * njc - 1)) / 12 - 34;
  loop assigns njc, u8e, wd;
*/
while (wd>3) {
      njc = njc + 1;
      u8e = u8e+njc*njc*njc*njc*njc;
      wd = 3;
  }
}