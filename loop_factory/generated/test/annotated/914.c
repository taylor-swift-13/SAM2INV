int main1(int z){
  int wy, ek, vd, b2, fhn;
  wy=z;
  ek=0;
  vd=1;
  b2=0;
  fhn=ek;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b2 == (vd - 1) * (vd - 1);
  loop invariant fhn == 4 * (vd - 1);
  loop invariant wy == z;
  loop invariant 1 <= vd;
  loop invariant fhn == ek * vd + 4 * (vd - 1);
  loop assigns b2, vd, fhn;
*/
while (vd<=wy) {
      b2 = b2+2*vd-1;
      vd += 1;
      fhn += ek;
      fhn += 4;
  }
}