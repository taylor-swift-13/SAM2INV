int main1(int m,int n){
  int l, j, i, k, b;

  l=m+19;
  j=0;
  i=m;
  k=-2;
  b=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == m + (k + b + 1) * j;
  loop invariant l == m + 19;
  loop invariant m == \at(m, Pre);

  loop invariant n == \at(n, Pre);
  loop invariant i - 4*j == \at(m,Pre) && i == \at(m,Pre) + 4*j;
  loop invariant j >= 0 && (l >= 0) ==> (j <= l) && l == m + 19;
  loop invariant i == m + 4*j;
  loop invariant k == -2;
  loop invariant b == 5;
  loop invariant j >= 0;
  loop invariant i == \at(m, Pre) + j*(k + b + 1);

  loop invariant l == \at(m, Pre) + 19;
  loop assigns i, j;
*/
while (j<l) {
      i = i+k+b;
      i = i+1;
      j = j+1;
  }

}
