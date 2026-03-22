int main1(int j,int h){
  int b1n, qb9, p, b;
  b1n=j+7;
  qb9=0;
  p=0;
  b=b1n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b1n == \at(j, Pre) + 7;
  loop invariant (qb9 == 0) || (qb9 == b1n);
  loop invariant (b == b1n) || (b == b1n + 1);
  loop invariant (qb9 == b1n) ==> (p == b*b);
  loop invariant (qb9 == 0) ==> (b == b1n && p == 0);
  loop assigns b, p, qb9;
*/
while (qb9<=b1n-1) {
      b += 1;
      p = b*b;
      qb9 = b1n;
  }
}