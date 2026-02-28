int main1(int k,int n){
  int m, t, v, y;

  m=n+20;
  t=0;
  v=0;
  y=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant m == n + 20;
  loop invariant n == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (m >= 0) ==> (v <= m);

  loop invariant 0 <= v;
  loop assigns v;
*/
while (v<m) {
      if (v<m) {
          v = v+1;
      }
  }

}
