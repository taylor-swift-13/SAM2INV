int main1(){
  int a7, sj, rsf, j1;
  a7=28;
  sj=0;
  rsf=a7;
  j1=sj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rsf == 4*sj + a7;
  loop invariant j1 == sj;
  loop invariant a7 == 28;
  loop invariant 0 <= j1 <= a7;
  loop assigns sj, rsf, j1;
*/
while (sj < a7) {
      sj += 1;
      rsf++;
      j1 += 1;
      rsf = rsf + 3;
  }
}