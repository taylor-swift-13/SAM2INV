int main1(int a,int b,int n,int p){
  int e, w, v, x, f, l, y;

  e=(n%26)+20;
  w=3;
  v=w;
  x=a;
  f=n;
  l=6;
  y=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= 3;
  loop invariant x == a + 3 * (v - 3) + ((v - 3) * (v - 2)) / 2 + (v - 3) * f;
  loop invariant x - f*v - v*(v+1)/2 == a - 3*f - 6;
  loop invariant x == a - 9 - 3*n + 3*v + n*v + ((v - 3) * (v - 2)) / 2;
  loop invariant f == n;
  loop invariant f == \at(n, Pre);
  loop invariant x == a + (v - 3) * (f + 3) + ((v - 3) * (v - 2)) / 2;
  loop invariant 2*(x - a) == (v - 3) * (v + 2*f + 4);
  loop assigns v, x;
*/
while (1) {
      v = v+1;
      x = x+v;
      x = x+f;
  }

}
