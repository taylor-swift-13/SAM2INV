int main1(){
  int n7, zo3, wgd3, k0, bxo;
  n7=1+4;
  zo3=0;
  wgd3=25;
  k0=zo3;
  bxo=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k0 == zo3;
  loop invariant wgd3 == 25 + zo3;
  loop invariant bxo == 4 + n7 * zo3;
  loop invariant (0 <= zo3);
  loop invariant (zo3 <= n7);
  loop invariant n7 == 5;
  loop assigns k0, wgd3, bxo, zo3;
*/
while (1) {
      k0 = (1)+(k0);
      wgd3++;
      bxo = bxo + n7;
      zo3 += 1;
      if (zo3>=n7) {
          break;
      }
  }
}