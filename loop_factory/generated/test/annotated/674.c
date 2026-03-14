int main1(){
  int li, ul8, lb, n, te, ds9n;
  li=1;
  ul8=li;
  lb=ul8;
  n=0;
  te=0;
  ds9n=li;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant li == 1;
  loop invariant te >= 0;
  loop invariant lb == 1 + te*(te+1)/2;
  loop invariant te <= n;
  loop invariant ul8 == 0 || ul8 == 1;
  loop assigns te, n, lb, ul8;
*/
while (1) {
      if (!(ul8>=1)) {
          break;
      }
      te = te + li;
      n += lb;
      lb = lb + te;
      ul8 = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ds9n == 1;
  loop invariant ul8 >= 0;
  loop invariant li % 3 == 1;
  loop invariant li >= 1;
  loop invariant lb >= 1;
  loop invariant n >= 0;
  loop assigns ul8, lb, li, n;
*/
while (ds9n*2<=n) {
      ul8 = ul8 + li;
      lb += n;
      li = li + 3;
      n = (ds9n*2)-1;
  }
}