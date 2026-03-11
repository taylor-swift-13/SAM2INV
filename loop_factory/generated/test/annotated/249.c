int main1(){
  int nj, k3, czd, zx5, j1;
  nj=20;
  k3=0;
  czd=0;
  zx5=0;
  j1=nj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (czd == zx5);
  loop invariant (j1 == 20 + (zx5 * (zx5 + 1)) / 2);
  loop invariant 0 <= zx5;
  loop invariant zx5 <= nj;
  loop invariant nj == 20;
  loop assigns zx5, czd, j1;
*/
while (zx5<nj) {
      zx5++;
      czd = czd + 1;
      j1 = j1 + zx5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns j1, nj;
*/
while (nj<k3) {
      j1 += 1;
      nj = nj + 1;
      j1 = j1 + czd;
  }
}