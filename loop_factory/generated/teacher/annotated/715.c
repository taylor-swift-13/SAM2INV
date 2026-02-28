int main1(int a,int b,int k,int p){
  int r, h, u, f, j, x, v, e;

  r=a-5;
  h=0;
  u=p;
  f=r;
  j=0;
  x=2;
  v=h;
  e=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant h >= 0;
  loop invariant r == a - 5;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant ((f == a - 5) || (f == 0));
  loop invariant ((u == p) || (u == p % 5));
  loop invariant (j == 0);
  loop invariant (r == a - 5);
  loop invariant (h >= 0);
  loop invariant ((x == 2) || (x == 0));
  loop invariant (h == 0) || (e == u*u);
  loop assigns x, u, f, e, h;
*/
while (1) {
      x = x*x+u;
      u = u%5;
      f = f*j;
      x = x*f;
      x = x*2;
      e = u*u;
      h = h+1;
  }

}
