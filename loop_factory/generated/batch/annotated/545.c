int main1(int m,int n){
  int b, t, p;

  b=m;
  t=0;
  p=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant b == m;
  loop invariant p >= m;
  loop invariant m == \at(m, Pre);
  loop invariant p >= \at(m, Pre);
  loop invariant b == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop assigns p;
*/
while (1) {
      p = p+4;
      if (t+7<=m+b) {
          p = p*p+p;
      }
      else {
          p = p*p+p;
      }
  }

}
