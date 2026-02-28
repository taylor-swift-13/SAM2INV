int main1(int b,int m,int p,int q){
  int g, v, c, x, f, y, o;

  g=q+19;
  v=g;
  c=g;
  x=p;
  f=b;
  y=3;
  o=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= g;
  loop invariant c - g == 3*(v - g);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g == q + 19;
  loop invariant c == 3*v - 2*g;
  loop invariant g == \at(q, Pre) + 19;
  loop invariant c >= g;
  loop invariant c - v == 2*(v - g);
  loop assigns c, v;
*/
while (1) {
      if (v>=g) {
          break;
      }
      c = c+1;
      v = v+1;
      c = c+2;
  }

}
