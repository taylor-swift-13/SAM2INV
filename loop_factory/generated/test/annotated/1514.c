int main1(){
  int t, y, x, ag5k, kme, dps8, y5, yxo;
  t=1+23;
  y=0;
  x=0;
  ag5k=0;
  kme=0;
  dps8=0;
  y5=0;
  yxo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x + ag5k + kme + dps8 == y;
  loop invariant 0 <= y <= 25;
  loop invariant (y == 0) ==> (x == 0 && ag5k == 0 && kme == 0 && dps8 == 0 && y5 == 0 && yxo == 0);
  loop invariant 0 <= yxo;
  loop invariant 0 <= y5;
  loop invariant (0 <= dps8);
  loop invariant yxo <= 7*y;
  loop invariant t == 24;
  loop invariant 0 <= x;
  loop invariant 0 <= ag5k;
  loop invariant 0 <= kme;
  loop assigns x, ag5k, kme, dps8, y, yxo, y5;
*/
while (1) {
      if (!(y<t+(1%7))) {
          break;
      }
      if (y%11==0) {
          x = x + 1;
      }
      else {
          if (y%10==0) {
              ag5k = ag5k + 1;
          }
          else {
              if (y%8==0) {
                  kme += 1;
              }
              else {
                  if (1) {
                      dps8 += 1;
                  }
              }
          }
      }
      y++;
      yxo = yxo+y%8;
      y5 += x;
  }
}