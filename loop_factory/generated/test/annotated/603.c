int main1(){
  int g5d, l4m, bqr, q8k0;
  g5d=1*2;
  l4m=0;
  bqr=3;
  q8k0=9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q8k0 == 9 + 6*l4m;
  loop invariant bqr == 3 + 6*l4m;
  loop invariant (0 <= l4m && l4m <= g5d);
  loop invariant (g5d == 2);
  loop assigns q8k0, l4m, bqr;
*/
while (1) {
      if (!(l4m<g5d)) {
          break;
      }
      q8k0 += 6;
      l4m += 1;
      bqr += 6;
  }
}