int main1(int l,int r){
  int y2h, mc, q1, sp9a, zj;
  y2h=52;
  mc=0;
  q1=0;
  sp9a=0;
  zj=mc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sp9a >= 0;
  loop invariant sp9a <= y2h;
  loop invariant l == \at(l, Pre) + 2*sp9a;
  loop invariant q1 == sp9a * \at(l, Pre) + sp9a*(sp9a - 1);
  loop invariant r == \at(r, Pre) + y2h * sp9a;
  loop invariant y2h == 52;
  loop assigns sp9a, q1, l, r;
*/
while (sp9a<y2h) {
      sp9a = sp9a + 1;
      q1 += l;
      l += 2;
      r = r + y2h;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= zj;
  loop assigns zj, y2h, l, r;
*/
while (1) {
      if (!(zj<q1)) {
          break;
      }
      zj = zj + 1;
      y2h += l;
      l = l + 1;
      r = r+(y2h%8);
  }
}