int main1(){
  int gg, wm, y1, jizo, zz2, n0x;
  gg=1+22;
  wm=4;
  y1=-8;
  jizo=0;
  zz2=wm;
  n0x=gg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zz2 + gg - wm == 23;
  loop invariant gg >= wm;
  loop invariant jizo <= 0;
  loop invariant zz2 >= 4;
  loop assigns zz2, jizo, n0x, gg;
*/
while (wm+1<=gg) {
      zz2 = (zz2+gg)+(-(wm));
      jizo = jizo+y1*wm;
      n0x += jizo;
      gg = (wm+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gg >= jizo;
  loop assigns wm, zz2, n0x, jizo;
*/
while (1) {
      wm = wm+n0x*jizo;
      zz2 += jizo;
      n0x = n0x*n0x+n0x;
      jizo = jizo + 1;
      if (jizo>=gg) {
          break;
      }
  }
}