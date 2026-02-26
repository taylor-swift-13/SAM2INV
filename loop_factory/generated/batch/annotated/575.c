int main1(int m,int n){
  int b, t, p;

  b=m;
  t=0;
  p=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == m && m == \at(m, Pre) && n == \at(n, Pre) && (t == 0 ==> p == m) && (t > 0 ==> p >= 0);
  loop invariant t >= 0;
  loop invariant b == \at(m, Pre);
  loop invariant p >= \at(m, Pre);
  loop invariant b == m;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p >= m;
  loop invariant (t > 0) ==> p >= 0;
  loop assigns p, t;
*/
while (1) {
      if (t+6<=m+b) {
          p = p*p;
      }
      else {
          p = p*p+p;
      }
      t = t+1;
  }

}
