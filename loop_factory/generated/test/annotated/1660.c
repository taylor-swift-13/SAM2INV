int main1(int i){
  int dgp, zfq5, zgt, x4;
  dgp=20;
  zfq5=0;
  zgt=i;
  x4=dgp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x4 == dgp + (zgt - i) * i + ((zgt - i) * (zgt - i - 1)) / 2;
  loop invariant zgt >= i;
  loop invariant x4 == 20 + (zgt - \at(i,Pre)) * \at(i,Pre)
                      + ((zgt - \at(i,Pre)) * (zgt - \at(i,Pre) - 1)) / 2;
  loop invariant zgt <= \at(i,Pre) + zfq5;
  loop invariant zfq5 <= dgp;
  loop invariant 0 <= zfq5;
  loop invariant dgp == 20;
  loop invariant x4 >= 20;
  loop invariant i == \at(i,Pre);
  loop assigns zfq5, zgt, x4;
*/
while (zfq5 < i && zfq5 < dgp) {
      zfq5 = zfq5 + (dgp / (zfq5 + 1));
      x4 = x4 + zgt;
      zgt += 1;
  }
}