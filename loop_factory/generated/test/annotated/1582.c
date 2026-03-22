int main1(){
  int uxl, gk, nn, ho, im, j, u, z, v6h, i1p, b0k;
  uxl=40;
  gk=uxl;
  nn=1;
  ho=0;
  im=gk;
  j=0;
  u=uxl;
  z=0;
  v6h=0;
  i1p=uxl;
  b0k=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (im - b0k - i1p) == 0;
  loop invariant gk == i1p;
  loop invariant (i1p + ho) == 40;
  loop invariant (i1p - nn) == 39;
  loop invariant b0k >= 0;
  loop invariant v6h >= 0;
  loop invariant gk >= 40;
  loop invariant j == 0;
  loop invariant uxl == 40;
  loop invariant (2*b0k == gk*gk - gk - 1560);
  loop invariant i1p >= 40;
  loop invariant b0k == (i1p - 40) * 40 + ((i1p - 40) * (i1p - 41)) / 2;
  loop assigns nn, ho, u, v6h, im, z, b0k, i1p, gk;
*/
while (gk-1>=0) {
      nn++;
      ho = ho - 1;
      if (j<v6h+1) {
          u = i1p-u;
      }
      if (u<i1p+1) {
          v6h += gk;
      }
      im += gk;
      z = im+j+u;
      b0k += gk;
      im++;
      i1p = (1)+(i1p);
      u += gk;
      gk = gk + 1;
  }
}