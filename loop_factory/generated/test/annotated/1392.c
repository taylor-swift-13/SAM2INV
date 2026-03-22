int main1(int n,int u){
  int l, ps, fc, bfx, vd, y8d;
  l=17;
  ps=0;
  fc=1;
  bfx=6;
  vd=0;
  y8d=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fc == vd*vd + 5*vd + 1;
  loop invariant bfx == 6 + 2*vd;
  loop invariant ps == (vd*vd*vd + 6*vd*vd - 4*vd) / 3;
  loop invariant (0 <= vd);
  loop invariant (vd <= l+1);
  loop assigns vd, ps, fc, bfx, y8d;
*/
while (vd<=l) {
      vd += 1;
      ps = ps + fc;
      fc += bfx;
      y8d = y8d + fc;
      bfx += 2;
      y8d = y8d*2;
  }
}