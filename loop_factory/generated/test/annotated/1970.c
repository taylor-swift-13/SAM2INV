int main1(int q){
  int s, gnwb, tx, cra;
  s=q;
  gnwb=0;
  tx=0;
  cra=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == q;
  loop invariant gnwb >= 0;
  loop invariant tx == gnwb * gnwb;
  loop invariant cra == q + (gnwb * (gnwb + 1) * (2 * gnwb + 1)) / 6;
  loop invariant (s >= 0) ==> (gnwb <= s);
  loop invariant q == \at(q, Pre);
  loop assigns tx, cra, gnwb;
*/
while (1) {
      if (!(gnwb < s)) {
          break;
      }
      tx = tx + 2*gnwb + 1;
      cra += tx;
      gnwb++;
  }
}