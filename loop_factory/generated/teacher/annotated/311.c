int main1(int m,int q){
  int n, j, l;

  n=m;
  j=0;
  l=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == m;
  loop invariant l >= m;
  loop invariant (l - m) % 12 == 0;
  loop invariant l >= n;
  loop invariant (l - n) % 12 == 0;
  loop invariant l >= \at(m,Pre);
  loop invariant (l - \at(m,Pre)) % 12 == 0;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(m,Pre);
  loop assigns l;
*/
while (1) {
      l = l+4;
      l = l+8;
  }

}
