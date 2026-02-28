int main1(int n,int p){
  int m, j, q;

  m=34;
  j=m+6;
  q=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= 40;
  loop invariant j >= 1;
  loop invariant m == 34;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j <= m + 6;
  loop assigns j;
*/
while (j>1) {
      j = j/2;
  }

}
