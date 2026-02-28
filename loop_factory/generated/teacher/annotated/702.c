int main1(int a,int m,int p,int q){
  int n, h, v, x, r, d;

  n=53;
  h=0;
  v=h;
  x=-2;
  r=h;
  d=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant x == -2;
  loop invariant r == 0;
  loop invariant d == 0;
  loop invariant h >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant n == 53;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns v, x, r, d, h;
*/
while (1) {
      v = v*2;
      x = x+v;
      r = r%2;
      if (v+4<n) {
          d = v*v;
      }
      h = h+1;
  }

}
