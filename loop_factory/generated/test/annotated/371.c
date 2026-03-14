int main1(){
  int cgr, n, l92, x, lc2p;
  cgr=1;
  n=0;
  l92=0;
  x=0;
  lc2p=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x <= 6;
  loop invariant n >= 0;
  loop invariant l92 == x;
  loop invariant n % 4 == 0;
  loop invariant lc2p + l92 == 6;
  loop assigns n, l92, x, lc2p;
*/
while (1) {
      if (!(lc2p>=1)) {
          break;
      }
      n = n+1*1;
      l92 = l92+1*1;
      x = x+1*1;
      lc2p--;
      n = n*2+2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= lc2p <= 8;
  loop invariant cgr >= 1;
  loop assigns lc2p, cgr;
*/
while (1) {
      if (!(lc2p>cgr)) {
          break;
      }
      lc2p -= cgr;
      cgr++;
      cgr = cgr*2;
      lc2p = (cgr)+(lc2p);
      lc2p = lc2p%9;
  }
}