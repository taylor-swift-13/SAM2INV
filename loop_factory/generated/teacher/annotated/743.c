int main1(int b,int k,int n,int p){
  int x, y, t, v, r, o, z, i;

  x=n;
  y=0;
  t=0;
  v=n;
  r=b;
  o=p;
  z=4;
  i=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 3*(r - \at(b, Pre));
  loop invariant v == 2*(r - \at(b, Pre)) + \at(n, Pre);
  loop invariant x == n;
  loop invariant r >= \at(b, Pre);
  loop invariant t >= 0;
  loop invariant v >= \at(n, Pre);
  loop invariant t == 3*(r - b);
  loop invariant v - n == 2*(r - b);
  loop invariant r >= b;
  loop invariant 2*t == 3*(v - n);
  loop invariant t % 12 == 0;
  loop invariant (r - b) % 4 == 0;
  loop invariant x == \at(n, Pre);
  loop invariant v >= n;
  loop assigns t, v, r;
*/
while (1) {
      t = t+8;
      v = v+8;
      t = t+4;
      r = r+4;
  }

}
