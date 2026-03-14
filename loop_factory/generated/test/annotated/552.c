int main1(){
  int yk, bj, k7;
  yk=1;
  bj=1;
  k7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yk == 1;
  loop invariant k7 == 2*bj - 2;
  loop invariant bj >= 1;
  loop assigns bj, k7;
*/
while (1) {
      if (!(bj<yk)) {
          break;
      }
      bj = 2*bj;
      k7 = k7 + 1;
      k7 += k7;
  }
}