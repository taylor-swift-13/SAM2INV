int main1(int a,int p){
  int n, v, q, w, t, y;

  n=39;
  v=1;
  q=0;
  w=a;
  t=n;
  y=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q <= n;
  loop invariant q >= 0;
  loop invariant t >= y;
  loop invariant t <= n;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q >= 0 && (t == 39 || t == -6) && y == -6;
  loop invariant y <= t;
  loop invariant t == y || t == 39;
  loop invariant n == 39;
  loop invariant ((q == 0) ==> (t == 39)) && ((q > 0) ==> (t == -6)) && ((t == 39) ==> (q == 0));
  loop invariant t <= 39;
  loop assigns q, t;
*/
while (q<n) {
      q = q+1;
      if (y<=t) {
          t = y;
      }
  }

}
