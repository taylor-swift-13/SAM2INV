int main1(int w){
  int s, qt8, q, tgw;
  s=(w%10)+16;
  qt8=-5;
  q=0;
  tgw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == tgw * w;
  loop invariant 0 <= tgw;
  loop invariant tgw <= s;
  loop assigns tgw, q;
*/
while (tgw<s) {
      tgw += 1;
      q = q + w;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == tgw * w;
  loop invariant 0 <= tgw;
  loop assigns tgw, q;
*/
while (1) {
      if (!(tgw<qt8)) {
          break;
      }
      tgw += 1;
      q = q + w;
  }
}