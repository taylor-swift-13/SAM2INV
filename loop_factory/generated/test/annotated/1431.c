int main1(int q){
  int nt, n, vyuv;
  nt=0;
  n=76;
  vyuv=38;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nt;
  loop invariant nt <= 38;
  loop invariant vyuv >= 0;
  loop invariant n + nt == 76;
  loop invariant vyuv == 38 - nt;
  loop assigns vyuv, n, nt;
*/
while (vyuv>0) {
      vyuv--;
      n = n - 1;
      nt++;
  }
}