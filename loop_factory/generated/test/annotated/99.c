int main1(int p,int v){
  int n, wc6, x;
  n=75;
  wc6=0;
  x=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre) + wc6 * n;
  loop invariant 0 <= wc6 <= n;
  loop invariant n == 75;
  loop invariant (wc6 < n/2) ==> (x == v);
  loop invariant (wc6 >= n/2) ==> (x == v + 4*(wc6 - n/2));
  loop assigns x, wc6, p;
*/
while (wc6<=n-1) {
      if (!(!(wc6>=n/2))) {
          x += 4;
      }
      wc6 += 1;
      p += n;
  }
}