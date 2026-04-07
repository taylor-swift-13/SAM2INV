int main1(int n){
  int t30, qk, q3m, lb9;
  t30=49;
  qk=0;
  q3m=0;
  lb9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lb9 == qk;
  loop invariant q3m == qk * n;
  loop invariant 0 <= lb9;
  loop invariant lb9 <= t30;
  loop assigns q3m, qk, lb9;
*/
while (qk < t30) {
      q3m += n;
      qk++;
      lb9 = qk;
  }
}