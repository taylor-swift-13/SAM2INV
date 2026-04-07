int main1(int a){
  int r5, ja, or, xzc, rl;
  r5=(a%14)+14;
  ja=0;
  or=r5;
  xzc=-3;
  rl=ja;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rl == ja * xzc;
  loop invariant ja <= r5;
  loop invariant r5 == (\at(a, Pre) % 14) + 14;
  loop invariant (or - rl - ja) == r5;
  loop invariant (or + 2 * ja) == r5;
  loop invariant xzc == -3;
  loop invariant ja >= 0;
  loop assigns ja, or, rl;
*/
while (1) {
      if (!(ja < r5)) {
          break;
      }
      ja += 1;
      or = or + xzc;
      rl = rl + xzc;
      or = or + 1;
  }
}