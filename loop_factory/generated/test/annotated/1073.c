int main1(int j){
  int gwhv, ma, ftjn, udj, qt2y, kue;
  gwhv=j+11;
  ma=0;
  ftjn=0;
  udj=0;
  qt2y=(j%18)+5;
  kue=gwhv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant udj == ma;
  loop invariant ftjn == ((j % 18) + 5 - qt2y) * (j * j);
  loop invariant ftjn == ma;
  loop invariant ma == ((\at(j,Pre) % 18) + 5 - qt2y) * j * j;
  loop invariant ma >= 0;
  loop assigns udj, ma, qt2y, ftjn, kue;
*/
while (1) {
      if (!(qt2y>=1)) {
          break;
      }
      udj = udj+j*j;
      ma = ma+j*j;
      qt2y -= 1;
      ftjn = ftjn+j*j;
      kue = kue+(ftjn%6);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant udj >= 0;
  loop invariant gwhv >= (\at(j, Pre) + 11);
  loop assigns gwhv, j, qt2y, udj;
*/
while (qt2y>gwhv) {
      qt2y -= gwhv;
      gwhv = gwhv + 1;
      j += gwhv;
      udj = udj*2;
      j = j + udj;
  }
}