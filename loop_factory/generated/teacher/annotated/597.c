int main1(int a,int n){
  int b, m, p, e;

  b=n+14;
  m=0;
  p=b;
  e=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == n + 14;
  loop invariant m >= 0;

  loop invariant p >= b;
  loop invariant p >= b + 2*m;
  loop invariant (m == 0) ==> (p == b);
  loop invariant (m >= 1) ==> (p >= b + 2);
  loop assigns m, p;
*/
while (1) {
      if (m>=b) {
          break;
      }
      p = p+2;
      m = m+1;
      p = p*p+p;
  }

}
