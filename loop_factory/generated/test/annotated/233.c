int main1(int r,int b){
  int r9v, uc, t0j, hu, gkx8;
  r9v=161;
  uc=r9v;
  t0j=-6;
  hu=0;
  gkx8=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uc - b == r9v - \at(b, Pre);
  loop invariant gkx8 == -5 - ((uc - r9v) * (uc - r9v - 1)) / 2;
  loop invariant r9v == 161;
  loop invariant t0j == -6;
  loop invariant b >= \at(b, Pre);
  loop invariant hu <= 0;
  loop invariant 2 * hu == t0j * (uc - r9v) * (r9v + uc - 1);
  loop assigns b, gkx8, hu, uc;
*/
while (uc-2>=0) {
      b += 1;
      gkx8 = gkx8+r9v-uc;
      hu = hu+t0j*uc;
      uc = uc + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gkx8 >= t0j;
  loop invariant (gkx8 > t0j) ==> (
                r9v == 161
             && b - \at(b, Pre) == (uc - 161)
             && 2*(gkx8 + 5) + (uc - 161)*(uc - 162) == 0
             && hu + 3*(uc - 161)*(uc - 162) + 966*(uc - 161) == 0
           );
  loop invariant t0j == -6;
  loop invariant r9v >= 161;
  loop assigns hu, r9v, uc, gkx8;
*/
while (gkx8>t0j) {
      hu += 1;
      r9v += uc;
      uc = uc + hu;
      gkx8 = t0j;
  }
}