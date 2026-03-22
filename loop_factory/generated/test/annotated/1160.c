int main1(){
  int x6n, a, mhi, y, k5q;
  x6n=0;
  a=0;
  mhi=(1%28)+10;
  y=x6n;
  k5q=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mhi == (1 % 28) + 10 - a*(a-1)/2;
  loop invariant y == a * x6n;
  loop invariant k5q >= 10;
  loop invariant k5q <= 10 + 4*a;
  loop invariant x6n == 0;
  loop invariant a >= 0;
  loop assigns mhi, a, k5q, y;
*/
while (mhi>a) {
      mhi = mhi - a;
      a++;
      k5q = k5q+(mhi%5);
      y += x6n;
  }
}