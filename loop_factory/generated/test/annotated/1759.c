int main1(){
  int kk1, c, dt, wm, gg;
  kk1=1;
  c=0;
  dt=0;
  wm=kk1;
  gg=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gg >= 0;
  loop invariant (c == 0) ==> (gg == 0 && dt == 0 && wm == 1);
  loop invariant 0 <= c <= kk1;
  loop invariant wm >= 1;
  loop invariant gg == dt * c;
  loop assigns c, dt, gg, wm;
*/
while (c < kk1) {
      c = c + 1;
      dt += wm;
      gg += dt;
      wm = wm+(dt%4);
  }
}