int main1(){
  int elo, xp, g9, rwq;
  elo=(1%28)+8;
  xp=(1%22)+5;
  g9=0;
  rwq=25;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rwq == 7 + 2*elo;
  loop invariant elo > 0;
  loop invariant g9 >= 0;
  loop invariant 0 <= xp <= 6;
  loop invariant rwq >= 25;
  loop assigns g9, xp, elo, rwq;
*/
while (1) {
      if (!(xp!=0)) {
          break;
      }
      if (xp%2==1) {
          g9 += elo;
          xp -= 1;
      }
      xp = xp/2;
      elo = 2*elo;
      rwq = (elo)+(rwq);
  }
}