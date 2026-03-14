int main1(int q,int v){
  int q2, an6, h0x, zj, kzg9;
  q2=140;
  an6=3;
  h0x=11;
  zj=1;
  kzg9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kzg9 == an6 - 3;
  loop invariant 0 <= h0x;
  loop invariant h0x <= 11;
  loop invariant zj == an6 - 2;
  loop invariant an6 >= 3;
  loop assigns an6, h0x, kzg9, zj;
*/
for (; h0x>0&&zj<=q2; an6 = an6 + 1) {
      if (h0x>zj) {
          h0x -= zj;
      }
      else {
          h0x = 0;
      }
      kzg9 += 1;
      zj = zj + 1;
  }
}