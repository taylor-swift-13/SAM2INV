int main1(){
  int e8, sj, t4, k0q, r, ml, ycr, fz, u5z;
  e8=(1%13)+7;
  sj=0;
  t4=9;
  k0q=0;
  r=sj;
  ml=-3;
  ycr=sj;
  fz=e8;
  u5z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r >= sj;
  loop invariant 0 <= u5z;
  loop invariant 0 <= sj;
  loop invariant sj <= e8;
  loop invariant t4 + k0q == 9;
  loop invariant ycr == sj*(sj+1)/2;
  loop invariant fz == e8 + ((sj + 1) / 2);
  loop invariant u5z >= 0;
  loop invariant ml >= -3;
  loop invariant 0 <= t4 <= 9;
  loop invariant 0 <= k0q <= 9;
  loop invariant e8 == 8;
  loop invariant -3 <= ml;
  loop assigns t4, k0q, sj, r, u5z, fz, ycr, ml;
*/
while (sj<=e8-1) {
      if (!(!(sj%2==0))) {
          if (t4>0) {
              t4--;
              k0q++;
          }
      }
      else {
          if (k0q>0) {
              k0q -= 1;
              t4 = t4 + 1;
          }
      }
      sj += 1;
      r += t4;
      u5z += k0q;
      r = r + 1;
      fz = fz+(sj%2);
      ycr = ycr + sj;
      ml += r;
  }
}