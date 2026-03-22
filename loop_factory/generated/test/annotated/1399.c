int main1(){
  int j, zop, kt, x, s, mw, uj;
  j=1+13;
  zop=2;
  kt=j;
  x=zop;
  s=zop;
  mw=-4;
  uj=zop;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mw <= j + 1;
  loop invariant (kt - s) >= 12;
  loop invariant x >= 2;
  loop invariant s >= 2;
  loop invariant uj >= 2;
  loop invariant j == 14;
  loop invariant s == 2*mw + 10;
  loop assigns uj, x, kt, s, mw;
*/
while (1) {
      if (mw>j) {
          break;
      }
      kt += x;
      x = x + s;
      uj = uj+x+kt;
      s += 2;
      mw = (1)+(mw);
  }
}