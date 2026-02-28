int main1(int k,int q){
  int h, c, v, n, w, d;

  h=k;
  c=0;
  v=c;
  n=h;
  w=q;
  d=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant d > v;
  loop invariant h == k;
  loop invariant w == q;
  loop invariant n <= k;
  loop invariant d >= 3;
  loop invariant v <= d;
  loop invariant n <= \at(k, Pre);
  loop invariant ((q <= k) ==> (n == k || n == q)) && ((q > k) ==> (n == k)) && n <= k && d >= 3;
  loop invariant q == \at(q, Pre);
  loop invariant (n == h) || (n == w);
  loop assigns n, v, d;
*/
while (1) {
      if (w<=n) {
          n = w;
      }
      v = v+1;
      d = d*d+v;
  }

}
