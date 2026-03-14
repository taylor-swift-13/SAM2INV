int main1(){
  int c, hcwe, np2f, nk67, xs, d;
  c=(1%29)+7;
  hcwe=1;
  np2f=0;
  nk67=0;
  xs=hcwe;
  d=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant np2f == nk67;
  loop invariant xs >= 1;
  loop invariant d == c + np2f*(np2f+1)/2;
  loop invariant 0 <= nk67 <= c;
  loop assigns np2f, nk67, xs, d;
*/
while (1) {
      if (!(nk67<c)) {
          break;
      }
      np2f += 1;
      nk67 += 1;
      xs = xs*3+1;
      d += np2f;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hcwe >= 1;
  loop invariant nk67 >= 0;
  loop invariant np2f >= 0;
  loop invariant xs > 0;
  loop assigns xs, nk67, np2f, hcwe;
*/
while (1) {
      xs += nk67;
      nk67 = nk67*2;
      np2f = np2f + xs;
      hcwe = hcwe + 1;
      if (hcwe>=c) {
          break;
      }
  }
}