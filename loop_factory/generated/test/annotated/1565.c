int main1(){
  int dmg, th80, tyu, wl, n2p, xmu, j7s, j;
  dmg=71;
  th80=0;
  tyu=10;
  wl=10;
  n2p=0;
  xmu=dmg;
  j7s=0;
  j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tyu + wl == 20;
  loop invariant n2p == 0;
  loop invariant 0 <= th80 <= dmg;
  loop invariant tyu == 10 - 2 * th80;
  loop invariant j7s == th80*th80 + 11*th80;
  loop invariant j == 0;
  loop invariant xmu >= 71;
  loop invariant dmg == 71;
  loop assigns tyu, wl, n2p, th80, xmu, j7s;
*/
while (1) {
      if (!(th80<dmg)) {
          break;
      }
      if (!(n2p!=0)) {
          tyu -= 2;
          wl += 2;
          n2p = 0;
      }
      else {
          tyu += 2;
          wl -= 2;
          n2p = 1;
      }
      th80 = th80 + 1;
      if (xmu+7<dmg) {
          xmu = j-xmu;
      }
      j7s = j7s + wl;
      xmu = xmu+j7s+j;
      xmu++;
  }
}