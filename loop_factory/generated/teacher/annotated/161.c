int main1(int n){
  int l, d, x;

  l=68;
  d=0;
  x=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d;
  loop invariant d <= l;
  loop invariant n == \at(n, Pre);
  loop invariant (d==0 ==> x==68) && (d>0 ==> x == n - 4);
  loop invariant l == 68;
  loop invariant (d == 0) ==> (x == l);
  loop invariant (d > 0) ==> (x == n - 4);
  loop invariant 0 <= d <= l;
  loop invariant (d == 0 && x == 68) || (d > 0 && x == n - 4);
  loop invariant l == 68 && d >= 0 && d <= l && (d > 0 ==> x == n - 4) && (d == 0 ==> x == 68);
  loop invariant (d == 0) ==> (x == 68);
  loop assigns x, d;
*/
while (d<l) {
      x = n+(-4);
      d = d+1;
  }

}
