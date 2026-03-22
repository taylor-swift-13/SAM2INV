int main1(){
  int q6, lm, bz, uqx, dk4, m, pq9;
  q6=(1%15)+12;
  lm=q6;
  bz=(1%60)+60;
  uqx=(1%9)+2;
  dk4=0;
  m=0;
  pq9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= dk4;
  loop invariant dk4 <= (bz - 1) / uqx;
  loop invariant pq9 == lm * (dk4 * uqx + m);
  loop invariant 0 <= m <= uqx - 1;
  loop invariant 0 <= pq9;
  loop assigns m, dk4, pq9;
*/
while (1) {
      if (bz<=uqx*dk4+m) {
          break;
      }
      if (m==uqx-1) {
          m = 0;
          dk4++;
      }
      else {
          m++;
      }
      pq9 = pq9 + lm;
  }
}