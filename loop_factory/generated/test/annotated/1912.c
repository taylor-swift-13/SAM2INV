int main1(){
  int ec, nw, r0l, g5b, h, f, sic, ba;
  ec=59;
  nw=0;
  r0l=14;
  g5b=11;
  h=0;
  f=nw;
  sic=2;
  ba=nw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == nw;
  loop invariant h == 0;
  loop invariant r0l == 14 - 3 * nw;
  loop invariant g5b == 11 + 3 * nw;
  loop invariant ba == (nw * (nw + 1)) / 2;
  loop invariant sic <= 2 + nw * nw;
  loop invariant (0 <= nw && nw <= ec);
  loop invariant 0 <= nw <= ec;
  loop invariant sic >= 2 + ba;
  loop assigns r0l, g5b, h, nw, sic, f, ba;
*/
while (nw<ec) {
      if (!(h!=0)) {
          r0l = r0l - 3;
          g5b = g5b + 3;
          h = 0;
      }
      else {
          r0l = r0l + 3;
          g5b = g5b - 3;
          h = 1;
      }
      nw++;
      if ((nw%9)==0) {
          sic += f;
      }
      f = f + 1;
      ba = ba + nw;
      sic += f;
  }
}