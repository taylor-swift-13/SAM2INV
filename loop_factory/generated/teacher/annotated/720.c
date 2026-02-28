int main1(int k,int m,int n,int p){
  int l, v, u, x, y, h;

  l=14;
  v=1;
  u=n;
  x=p;
  y=-3;
  h=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 14;
  loop invariant v <= l;
  loop invariant v >= 1;

  loop invariant 1 <= v;

  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (v >= 2) ==> (u % 3 == 0);
  loop assigns u, v;
*/
while (1) {
      if (v>=l) {
          break;
      }
      u = u+2;
      v = v+1;
      u = u*3+3;
  }

}
