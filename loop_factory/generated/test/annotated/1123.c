int main1(){
  int lg, u, w, h, vg;
  lg=1*2;
  u=1;
  w=1*2;
  h=2;
  vg=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 1;
  loop invariant 2*h == w*w - w + 2;
  loop invariant w >= 2;
  loop invariant 0 <= lg <= 2;
  loop assigns h, w, lg;
*/
while (u*2<=lg) {
      h = h + w;
      w = w + u;
      lg = (u*2)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vg <= lg;
  loop invariant u == 1;
  loop invariant w >= 2;
  loop invariant h >= 2;
  loop assigns vg, w, h;
*/
while (vg<lg) {
      vg += 1;
      w += 1;
      h = h + u;
  }
}