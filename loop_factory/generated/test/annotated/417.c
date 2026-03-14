int main1(int h,int x){
  int rjq, f1, j1q, fefn, a3, hnt;
  rjq=h*3;
  f1=0;
  j1q=44;
  fefn=0;
  a3=1;
  hnt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= f1;
  loop invariant fefn + j1q == 44;
  loop invariant a3 == f1 + 1;
  loop invariant j1q >= 0;
  loop invariant fefn >= 0;
  loop invariant 0 <= hnt;
  loop invariant hnt <= a3;
  loop assigns f1, j1q, fefn, a3, hnt;
*/
for (; j1q>0&&f1<rjq; f1++) {
      if (j1q<=a3) {
          hnt = j1q;
      }
      else {
          hnt = a3;
      }
      fefn += hnt;
      a3++;
      j1q -= hnt;
  }
}