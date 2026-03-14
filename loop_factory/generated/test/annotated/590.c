int main1(){
  int dt, vgb, r2, smxf;
  dt=1;
  vgb=0;
  r2=dt;
  smxf=dt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r2 == 1 + 2 * vgb;
  loop invariant smxf == (vgb + 1) * (vgb + 1);
  loop invariant dt == 1;
  loop invariant smxf == r2 + vgb;
  loop assigns vgb, smxf, r2;
*/
while (vgb<dt) {
      if (!(!(vgb>=dt/2))) {
          r2 += 2;
      }
      vgb++;
      smxf += r2;
  }
}