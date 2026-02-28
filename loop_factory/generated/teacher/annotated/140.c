int main1(int b){
  int t, j, n;

  t=b;
  j=0;
  n=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant t == \at(b, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n >= 0;
  loop invariant n == j*(j-1)/2;
  loop invariant 0 <= j;
  loop invariant j <= t || t < 0;


  loop invariant 2*n == j*(j-1);
  loop invariant t == b;
  loop assigns n, j;
*/
while (j<t) {
      n = n+j;
      j = j+1;
  }

}
