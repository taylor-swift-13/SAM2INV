int main1(int m,int a){
  int u8jj, lao, vj, kz, n1;
  u8jj=65;
  lao=0;
  vj=40;
  kz=1;
  n1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lao == n1;
  loop invariant kz == n1 + 1;
  loop invariant 0 <= n1 <= u8jj;
  loop invariant vj <= u8jj;
  loop assigns vj, lao, kz, n1;
*/
while (1) {
      if (!(vj>0&&kz<=u8jj)) {
          break;
      }
      if (!(vj<=kz)) {
          vj = 0;
      }
      else {
          vj = vj - kz;
      }
      lao++;
      kz++;
      n1 = n1 + 1;
  }
}