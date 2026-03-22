int main1(int y,int u){
  int xo, eo1, jju, a9, is;
  xo=y;
  eo1=0;
  jju=eo1;
  a9=5;
  is=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a9 == 5;
  loop invariant jju == 0;
  loop invariant xo == \at(y, Pre);
  loop invariant ((jju == 0) ==> (a9 == 5)) &&
                 ((jju != 0) ==> ((a9 - 5) % jju == 0));
  loop invariant ((eo1 == 0 && xo == y) || (eo1 == xo));
  loop assigns a9, eo1;
*/
while (eo1<xo) {
      a9 = a9 + jju;
      eo1 = xo;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (xo - is * y) == \at(y, Pre) * (1 - \at(u, Pre));
  loop invariant xo == \at(y, Pre) + (is - \at(u, Pre)) * y;
  loop assigns xo, is;
*/
while (is<jju) {
      xo = xo + y;
      is++;
  }
}