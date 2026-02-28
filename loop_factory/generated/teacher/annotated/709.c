int main1(int b,int k,int n,int q){
  int l, x, v, f, y, h, j;

  l=k;
  x=2;
  v=l;
  f=n;
  y=q;
  h=-8;
  j=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= \at(k, Pre);

  loop invariant l == \at(k, Pre);
  loop invariant y == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant f == n + k*(v - k) + ((v - k)*(v - k + 1))/2;
  loop invariant (v > k) ==> (h == v + f + y);
  loop invariant (v == k) ==> (h == -8);
  loop invariant v >= k;


  loop invariant b == \at(b, Pre);

  loop assigns v, f, h;
*/
while (1) {
      v = v+1;
      f = f+v;
      h = v+f+y;
  }

}
