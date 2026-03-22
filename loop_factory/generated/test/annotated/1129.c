int main1(){
  int xfx2, il, ba, x1c, ya6y;
  xfx2=76;
  il=0;
  ba=(1%40)+2;
  x1c=0;
  ya6y=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya6y == 5;
  loop invariant 0 <= x1c;
  loop invariant xfx2 == 76;
  loop invariant (ba >= 1);
  loop invariant (ba <= xfx2);
  loop assigns x1c, ba, ya6y;
*/
while (ba!=x1c) {
      x1c = ba;
      ba = (ba+xfx2/ba)/2;
      ya6y = ya6y+ba-ba;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (il != 0) ==> ba == (il + xfx2/il) / 2;
  loop invariant xfx2 == 76;
  loop invariant il >= 0;
  loop invariant 0 <= x1c;
  loop invariant (ba >= 1);
  loop invariant (ba <= xfx2);
  loop assigns il, ba, x1c;
*/
while (1) {
      if (!(ba!=il)) {
          break;
      }
      il = ba;
      ba = (ba+xfx2/ba)/2;
      x1c = x1c+(ba%7);
  }
}