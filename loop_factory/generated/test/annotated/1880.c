int main1(){
  int h8, bb, aw, ok7, ln, mz, y, c5, xjc, yh7;
  h8=1+5;
  bb=0;
  aw=0;
  ok7=0;
  ln=0;
  mz=0;
  y=0;
  c5=0;
  xjc=6;
  yh7=h8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xjc == h8 + bb*(bb-1)/2;
  loop invariant c5 == bb*(bb+1)/2;
  loop invariant aw <= bb;
  loop invariant aw >= 0;
  loop invariant y >= 0;
  loop invariant yh7 >= 0;
  loop invariant ok7 >= 0;
  loop invariant ln == 0;
  loop invariant mz == 0;
  loop invariant (yh7 % h8) == 0;
  loop invariant (bb == 0) ==> (ok7 == 0);
  loop invariant (bb > 0) ==> (aw == bb - 1);
  loop invariant 0 <= bb;
  loop invariant xjc == 6 + bb*(bb-1)/2;
  loop invariant (bb == 0) ==> (y == 0);
  loop invariant (bb > 0) ==> (y == bb + 1);
  loop assigns aw, bb, c5, xjc, y, yh7, ln, mz, ok7;
*/
while (bb<h8+(1%7)) {
      if (!(!(bb%11==0))) {
          if (bb%10==0) {
              ok7 = ok7 + 1;
              y += 2;
          }
          else {
              if (bb%8==0) {
                  ln += 1;
                  y = y + 3;
              }
              else {
                  if (1) {
                      mz = mz + 1;
                      y += 4;
                  }
              }
          }
      }
      else {
          aw = aw + 1;
          y++;
      }
      bb++;
      xjc += aw;
      yh7 += yh7;
      c5 = c5+bb%10;
  }
}