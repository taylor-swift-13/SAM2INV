int main1(int h,int a){
  int fk30, sden, zs1, dn;
  fk30=46;
  sden=fk30;
  zs1=0;
  dn=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant sden <= fk30 && (dn == 1 || dn == -1);
  loop invariant 0 <= zs1 <= 4;
  loop invariant sden >= 46;
  loop invariant h - zs1 == \at(h, Pre);
  loop invariant h <= \at(h, Pre) + (fk30 - sden);
  loop invariant h >= \at(h, Pre) - (fk30 - sden);
  loop assigns {dn, h, sden, zs1};
*/
while (sden<fk30) {
      if (zs1>=4) {
          dn = -1;
      }
      if (zs1<=0) {
          dn = 1;
      }
      zs1 += dn;
      sden = sden + 1;
      h += dn;
  }
}