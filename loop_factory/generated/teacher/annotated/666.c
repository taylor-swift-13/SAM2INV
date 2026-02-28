int main1(int k,int p){
  int l, f, d, n, y, h;

  l=k+21;
  f=0;
  d=p;
  n=k;
  y=k;
  h=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == p + f + k * f * (f + 1) / 2;
  loop invariant n == k * (f + 1);
  loop invariant l == k + 21;
  loop invariant y == k;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant f >= 0;
  loop invariant d == p + f + (k * f * (f + 1)) / 2;




  loop assigns d, f, n;
*/
while (1) {
      if (f>=l) {
          break;
      }
      d = d+1;
      f = f+1;
      d = d+n;
      n = n+y;
  }

}
