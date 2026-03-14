int main1(){
  int nuo, xx, fl, mx, lx1;
  nuo=63;
  xx=0;
  fl=0;
  mx=0;
  lx1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mx == xx % 11;
  loop invariant lx1 == xx;
  loop invariant fl == xx / 11;
  loop invariant 0 <= xx;
  loop invariant xx <= nuo;
  loop assigns mx, lx1, fl, xx;
*/
while (1) {
      if (!(xx<nuo)) {
          break;
      }
      mx++;
      lx1++;
      if (mx>=11) {
          mx -= 11;
          fl = fl + 1;
      }
      xx = xx + 1;
  }
}