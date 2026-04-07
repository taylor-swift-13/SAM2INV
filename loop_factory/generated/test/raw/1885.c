int main1(){
  int y, mi0, n, ky, xh2, acof, muw, f5, q, sp69, pdl6;

  y=1*5;
  mi0=0;
  n=y;
  ky=-8;
  xh2=y;
  acof=y;
  muw=mi0;
  f5=0;
  q=1*3;
  sp69=y;
  pdl6=y;

  while (1) {
      if (!(mi0 < y)) {
          break;
      }
      n = (n + mi0) % 256;
      ky = (ky + xh2) % 97;
      f5 = (f5 + q) % 19;
      xh2 = (xh2 + pdl6) % 64;
      acof = (acof + muw) % 13;
      q = (q + sp69) % 23;
      sp69 = (sp69 + pdl6) % 29;
      pdl6 = (pdl6 + 1) % 31;
      mi0++;
      if (!(!((mi0%2)==0))) {
          muw += 2;
      }
      if (mi0<q+1) {
          muw = muw + muw;
      }
      muw = muw - muw;
  }

}
