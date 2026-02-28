int main1(int n,int p){
  int m, l, v, f, d, w;

  m=n;
  l=0;
  v=-3;
  f=l;
  d=2;
  w=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == n;
  loop invariant 0 <= d;
  loop invariant d <= 7;
  loop invariant v <= -3;
  loop invariant f <= 0;
  loop invariant d == 2;
  loop invariant f % 3 == 0;
  loop invariant v <= -2;
  loop assigns v, f, d;
*/
while (1) {
      v = v+1;
      f = f+v;
      v = v*2;
      f = f+v;
      d = d%8;
  }

}
