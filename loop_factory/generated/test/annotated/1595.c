int main1(){
  int r0, g, r5, m, ehk, b, fq, nzc, l7k, twvr;
  r0=1-5;
  g=0;
  r5=28;
  m=0;
  ehk=1;
  b=0;
  fq=r0;
  nzc=0;
  l7k=r0;
  twvr=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r5 >= 0;
  loop invariant m >= 0;
  loop invariant g >= 0;
  loop invariant ehk == 1 + g;
  loop invariant fq == r0 + 3*g;
  loop invariant nzc == r0*g + 3*g*(g+1)/2;
  loop invariant r5 + m == 28;
  loop invariant twvr >= 1;
  loop invariant fq == -4 + 3*g;
  loop invariant l7k == r0;
  loop assigns b, g, m, r5, ehk, l7k, twvr, fq, nzc;
*/
while (r5>0&&g<r0) {
      if (r5<=ehk) {
          b = r5;
      }
      else {
          b = ehk;
      }
      g++;
      m += b;
      r5 -= b;
      ehk = ehk + 1;
      if (l7k+7<r0) {
          l7k = fq-l7k;
      }
      twvr = twvr + r5;
      fq += 2;
      fq += 1;
      nzc = nzc + fq;
  }
}