int main1(int m,int q){
  int igv, cbd, z1qh, se4g, nyi, dtb, u, gb;
  igv=m-8;
  cbd=0;
  z1qh=4;
  se4g=4;
  nyi=0;
  dtb=4;
  u=0;
  gb=cbd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == cbd;
  loop invariant igv == \at(m, Pre) - 8;
  loop invariant dtb >= 4 && se4g >= 4 && dtb >= se4g;
  loop invariant z1qh >= 0 && nyi >= 0 && nyi <= cbd;
  loop invariant gb >= 0 && m >= \at(m, Pre);
  loop invariant cbd >= 0;
  loop invariant z1qh >= 0;
  loop invariant z1qh <= dtb;
  loop invariant se4g >= 4;
  loop invariant dtb >= 4;
  loop invariant nyi >= 0;
  loop invariant gb >= cbd;
  loop invariant m >= \at(m, Pre);
  loop invariant (cbd == u);
  loop invariant (0 <= cbd);
  loop invariant (0 <= z1qh && z1qh <= dtb);
  loop invariant (dtb >= 4);
  loop invariant (se4g >= 4);
  loop invariant (nyi >= 0);
  loop invariant (gb >= cbd);
  loop invariant (m >= \at(m, Pre));
  loop invariant 0 <= cbd;
  loop invariant (igv > 0) ==> (cbd <= igv);
  loop invariant 0 <= z1qh;
  loop invariant 0 <= nyi;
  loop invariant nyi <= cbd;
  loop invariant se4g >= 0;
  loop invariant dtb >= 0;
  loop invariant 0 <= u;
  loop invariant 0 <= z1qh && z1qh <= dtb;
  loop invariant 0 <= nyi && nyi <= cbd;
  loop invariant se4g <= 4 + cbd;
  loop invariant (u == cbd);
  loop invariant (0 <= u);
  loop invariant (z1qh >= 0);
  loop invariant (gb >= 0);
  loop invariant (se4g <= 4 + u);
  loop invariant (nyi <= u);
  loop invariant (dtb >= 4 + 5 * u);
  loop invariant (z1qh <= dtb);
  loop invariant cbd == u;
  loop invariant gb >= 0;
  loop invariant (cbd >= 0);
  loop invariant (nyi >= 0 && nyi <= u);
  loop invariant (z1qh >= 0 && z1qh <= dtb);
  loop invariant (se4g >= 4 && se4g <= (4 + u));
  loop invariant (dtb >= 4 && dtb >= z1qh);
  loop assigns cbd, z1qh, se4g, nyi, dtb, u, gb, m;
*/
while (1) {
      if (!(cbd<igv)) {
          break;
      }
      if (!(!(cbd%3==0))) {
          if (z1qh>0) {
              z1qh -= 1;
              nyi = nyi + 1;
          }
      }
      else {
          if (z1qh<dtb) {
              z1qh++;
              se4g += 1;
          }
      }
      cbd = cbd + 1;
      u = u + 1;
      dtb = dtb + se4g;
      dtb += 1;
      gb += dtb;
      m = m + gb;
  }
}