int main1(){
  int mnr, zsh, n4c, zw, ltp;
  mnr=1*4;
  zsh=mnr;
  n4c=0;
  zw=0;
  ltp=mnr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zsh == mnr;
  loop invariant ltp == mnr*(n4c+1);
  loop invariant zw == n4c*(n4c-1)/2;
  loop invariant n4c <= mnr;
  loop invariant 0 <= n4c;
  loop assigns zw, n4c, ltp;
*/
while (1) {
      if (!(n4c<=mnr-1)) {
          break;
      }
      zw = zw + n4c;
      n4c = n4c + 1;
      ltp = ltp + zsh;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mnr < ltp;
  loop invariant zsh > 0;
  loop invariant mnr >= 0;
  loop assigns zsh, mnr;
*/
while (1) {
      zsh = zsh + zsh;
      mnr = mnr + 1;
      if (mnr>=ltp) {
          break;
      }
  }
}