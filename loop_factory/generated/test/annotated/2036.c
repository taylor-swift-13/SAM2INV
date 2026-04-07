int main1(){
  int ahqp, n, lo6, j, kpy;
  ahqp=174;
  n=0;
  lo6=0;
  j=0;
  kpy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 3 * n;
  loop invariant lo6 == 0;
  loop invariant 0 <= n;
  loop invariant n <= ahqp;
  loop invariant 0 <= kpy;
  loop invariant kpy <= 6 * n;
  loop invariant ahqp == 174;
  loop assigns j, n, lo6, kpy;
*/
while (n < ahqp) {
      j = j + 3;
      n += 1;
      lo6 = lo6 + lo6;
      kpy = kpy+(j%7);
  }
}