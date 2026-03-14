int main1(int n){
  int k1, j5s, tx, zao;
  k1=16;
  j5s=0;
  tx=1;
  zao=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j5s <= k1;
  loop invariant 1 <= tx <= 9;
  loop invariant ((tx - j5s) % 2 != 0);
  loop invariant zao == 1 || zao == -1;
  loop invariant n == \at(n, Pre);
  loop assigns j5s, tx, zao;
*/
for (; j5s<k1; j5s++) {
      if (!(tx<9)) {
          zao = -1;
      }
      if (tx<=1) {
          zao = 1;
      }
      tx += zao;
  }
}