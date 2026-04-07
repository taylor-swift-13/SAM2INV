int main1(int c){
  int cl, ek, fg, j, zq2;
  cl=38;
  ek=0;
  fg=0;
  j=0;
  zq2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ek == 0) || (ek == cl);
  loop invariant (ek == 0) ==> (fg == 0 && j == 0 && zq2 == 0);
  loop invariant (ek == cl) ==> (fg == c && j == c && zq2 == c*c);
  loop invariant (
       (ek == 0 && fg == 0 && j == 0 && zq2 == 0)
       ||
       (ek == cl && fg == \at(c, Pre) && j == \at(c, Pre)
        && zq2 == (\at(c, Pre) * \at(c, Pre)))
    );
  loop invariant 0 <= cl - ek;
  loop invariant (0 <= ek && ek <= cl);
  loop assigns fg, zq2, j, ek;
*/
while (ek < cl) {
      fg = fg + c;
      zq2 = zq2 + fg*fg;
      j = j + fg;
      ek = cl;
  }
}