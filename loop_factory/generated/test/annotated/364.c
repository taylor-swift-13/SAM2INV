int main1(int k){
  int m, wq, t9wk, y7f6;
  m=k+6;
  wq=m+3;
  t9wk=m;
  y7f6=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m <= wq && wq <= m + 3 && ((wq - m) == 0 || (wq - m) == 3);
  loop invariant m == k + 6;
  loop assigns wq;
*/
while (1) {
      if (!(wq>m)) {
          break;
      }
      wq = wq - 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y7f6 >= -5;
  loop invariant t9wk >= m;
  loop assigns wq, t9wk, y7f6;
*/
while (wq>t9wk) {
      wq = wq - t9wk;
      t9wk = (1)+(t9wk);
      y7f6 = y7f6 + t9wk;
      y7f6 = y7f6*y7f6+y7f6;
  }
}