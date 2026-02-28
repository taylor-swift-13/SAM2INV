int main1(int b,int n,int p){
  int u, o, r, x, v, f;

  u=48;
  o=u;
  r=0;
  x=0;
  v=n;
  f=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (r <= u/2) ==> (x == r);
  loop invariant (r > u/2) ==> (x == u - r);
  loop invariant r <= u;
  loop invariant 0 <= r <= u;
  loop invariant 0 <= x;
  loop invariant u == 48;
  loop invariant 0 <= r;
  loop invariant ((r <= u/2 && x == r) || (r > u/2 && x == u - r));
  loop invariant x <= u/2;
  loop invariant (r < u/2) ==> (x == r);
  loop invariant (r >= u/2) ==> (x == u - r);
  loop assigns x, r;
*/
while (r<u) {
      if (r<u/2) {
          x = x+1;
      }
      else {
          x = x-1;
      }
      r = r+1;
  }

}
