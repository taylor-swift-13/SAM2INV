int main1(int g){
  int u, vb, uhf, dc, c24, bkb, nyt9, f, keo, xt, eu;
  u=g+4;
  vb=0;
  uhf=0;
  dc=0;
  c24=0;
  bkb=0;
  nyt9=-5;
  f=-8;
  keo=vb;
  xt=-8;
  eu=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vb;
  loop invariant g == \at(g, Pre) + vb;
  loop invariant f == -8 + vb;
  loop invariant eu == -4 + 2*vb;
  loop invariant c24 == vb / 2;
  loop invariant bkb == vb / 2;
  loop invariant uhf == (vb + 1) / 2;
  loop invariant (u < 7) ==> (keo == 0);
  loop invariant nyt9 == -5 + 3*(vb/2) + 2*(vb%2);
  loop invariant uhf == dc;
  loop invariant u == \at(g, Pre) + 4;
  loop invariant xt == -8 - ((vb + 1) / 2);
  loop assigns g, vb, f, eu, xt, nyt9, uhf, dc, c24, bkb, keo;
*/
while (1) {
      if (!(vb < u)) {
          break;
      }
      if ((vb % 2) == 0) {
          uhf += 1;
          dc++;
      }
      else {
          c24 = c24 + 1;
          bkb = bkb + 1;
      }
      vb = vb + 1;
      if (!(!(vb+7<=vb+u))) {
          keo += vb;
      }
      f = f + 1;
      g++;
      xt = xt+c24-uhf;
      nyt9 = nyt9+uhf-bkb;
      eu += 2;
      nyt9 += 1;
  }
}