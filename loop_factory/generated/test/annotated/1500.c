int main1(){
  int yw, wt47, t0t, w, yc, am;
  yw=1;
  wt47=0;
  t0t=-2;
  w=wt47;
  yc=yw;
  am=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant am == wt47 * yw;
  loop invariant w == wt47 * yc;
  loop invariant (wt47 == 0) ==> (t0t == -2);
  loop invariant 0 <= wt47;
  loop invariant wt47 <= yw;
  loop assigns am, t0t, w, wt47;
*/
while (wt47 < yw) {
      t0t = t0t * w;
      wt47 = wt47 + 1;
      w += yc;
      am += yw;
  }
}