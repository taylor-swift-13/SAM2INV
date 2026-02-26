int main1(int a,int n){
  int w, u, v, q;

  w=n;
  u=w;
  v=u;
  q=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == n;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= n;
  loop invariant ((v - n) % 2) == 0;
  loop invariant (v - n) % 2 == 0;
  loop invariant w == \at(n, Pre);
  loop invariant v >= \at(n, Pre);
  loop invariant (v - \at(n, Pre)) % 2 == 0;
  loop invariant v <= w;
  loop invariant v <= w + 1;
  loop assigns v;
*/
while (v<w) {
      if (v<w) {
          v = v+1;
      }
      v = v+1;
  }

}
