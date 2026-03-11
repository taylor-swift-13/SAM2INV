int main1(){
  int th, ziz, n;
  th=37;
  ziz=1;
  n=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 0;
  loop invariant n <= 4*ziz - 4;
  loop invariant (ziz == 1  && n == 0) ||
                 (ziz == 2  && n == 4) ||
                 (ziz == 4  && n == 8) ||
                 (ziz == 8  && n == 12) ||
                 (ziz == 16 && n == 16) ||
                 (ziz == 32 && n == 20) ||
                 (ziz == 64 && n == 21);
  loop assigns n, ziz;
*/
while (ziz<th) {
      n = (1)+(n);
      ziz = 2*ziz;
      if (ziz<th+1) {
          n = n + 3;
      }
  }
/*@
  assert th == 37;
  assert ziz == 64;
  assert n == 21;
*/
}
