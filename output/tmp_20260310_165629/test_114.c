int main1(int u){
  int iod, l5, zf, l0, r8ph, gt, l;
  iod=79;
  l5=0;
  zf=0;
  l0=0;
  r8ph=0;
  gt=0;
  l=iod;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l5 <= iod;
  loop invariant l >= iod;
  loop invariant r8ph <= (iod - 1) / 18 + 1;
  loop invariant 0 <= gt <= iod;
  loop invariant 0 <= r8ph <= iod;
  loop invariant zf == 0;
  loop invariant 0 <= l0;
  loop invariant gt <= l5;
  loop invariant r8ph <= (l5 + 17) / 18;
  loop assigns l, l5, gt, r8ph, l0, zf;
*/
while (l5<iod) {
      if (!(!(l5%9==0))) {
          if (l5%6==0) {
              r8ph += 1;
          }
          else {
              if (l5%3==0) {
                  l0 = l0 + 1;
              }
              else {
                  zf += 1;
              }
          }
      }
      else {
          gt = gt + 1;
      }
      l5 += 1;
      l = l + gt;
  }
/*@
  assert (iod == 79) &&
         (l5 == iod) &&
         (zf == 0) &&
         (0 <= gt && gt <= l5) &&
         (r8ph <= (l5 + 17) / 18) &&
         (0 <= l0);
*/
}
