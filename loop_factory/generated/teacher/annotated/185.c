int main1(int n,int p){
  int m, j, q;

  m=34;
  j=m;
  q=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 34;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j <= 34;
  loop invariant j >= 1;
  loop invariant (j % 3) == 1;

  loop invariant j <= m;
  loop invariant (m - j) % 3 == 0;
  loop invariant j % 3 == 1;
  loop invariant q % 34 == 0;
  loop invariant q >= 34;

  loop assigns j, q;
*/
while (j>2) {
      q = q+q;
      j = j-3;
  }

}
