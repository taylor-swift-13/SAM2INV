int main1(){
  int wuu, hlpc, g8, n8, gw, u;
  wuu=1;
  hlpc=0;
  g8=0;
  n8=0;
  gw=(1%18)+5;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (g8 == hlpc);
  loop invariant (hlpc == n8);
  loop invariant (gw + n8 == 6);
  loop invariant (wuu == 1);
  loop invariant (0 <= n8 && n8 <= 6);
  loop invariant u >= 0;
  loop assigns gw, n8, g8, hlpc, u;
*/
while (1) {
      if (!(gw>=1)) {
          break;
      }
      gw--;
      n8 = n8+1*1;
      g8 = g8+1*1;
      hlpc = hlpc+1*1;
      u = u*3+(gw%2)+0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= gw;
  loop invariant gw <= 6;
  loop invariant wuu >= 1;
  loop assigns gw, wuu;
*/
while (gw>wuu) {
      gw = gw - wuu;
      wuu += 1;
      wuu = wuu*wuu+wuu;
  }
}