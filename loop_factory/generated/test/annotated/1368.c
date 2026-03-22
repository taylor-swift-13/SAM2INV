int main1(int g){
  int bxu, uhp, q9, sq;
  bxu=g+16;
  uhp=bxu+4;
  q9=0;
  sq=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*(uhp - bxu) + q9 == 8;
  loop invariant 0 <= uhp - bxu;
  loop invariant q9 == ((bxu + 4 - uhp) / 2) * sq;
  loop invariant ((uhp - bxu) % 2) == 0;
  loop assigns q9, uhp;
*/
while (uhp-bxu>0) {
      q9 += sq;
      uhp -= 2;
  }
}