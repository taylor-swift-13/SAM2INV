int main1(int i){
  int pgj, n, xb, num;
  pgj=i-7;
  n=0;
  xb=0;
  num=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i,Pre) + xb * pgj;
  loop invariant (xb == 0 ==> num == 0) && (xb >= 1 ==> num + xb == pgj + 1);
  loop invariant n == 0;
  loop invariant pgj == \at(i,Pre) - 7;
  loop invariant xb >= 0;
  loop invariant i == \at(i, Pre) + xb * pgj && ((xb == 0 && num == 0) || (num + xb == pgj + 1));
  loop assigns i, xb, num;
*/
while (n<=pgj-2) {
      num = pgj-xb;
      xb += 1;
      i = i + pgj;
  }
}