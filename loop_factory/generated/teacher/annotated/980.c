int main1(int m,int n){
  int r, g, v, e;

  r=21;
  g=r;
  v=g;
  e=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g + 3*v == 84;
  loop invariant 2*e == v*v + v - 420;
  loop invariant r == 21;
  loop invariant g >= 0;
  loop invariant g <= 21;
  loop invariant g + 3 * v == 84;
  loop invariant 2 * e == (v - 20) * (v + 21);
  loop invariant g % 3 == 0;
  loop invariant g >= 0 && v >= 21;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant 3*(v - r) == r - g;
  loop invariant e == r + (v - r)*r + ((v - r)*(v - r + 1))/2;
  loop invariant g >= 0 && g <= r;
  loop invariant v >= r;
  loop invariant 3*v + g == 84;
  loop invariant e - v*(v+1)/2 == -210;
  loop invariant 0 <= g && g <= 21;
  loop invariant v >= 21;
  loop invariant 2 * e == (v + r) * (v - r + 1);
  loop invariant 2*e == 2*r + (v - r)*(r + v + 1);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant e == r + r*(v - r) + ((v - r)*(v - r + 1))/2;
  loop invariant g == 84 - 3*v;
  loop invariant e >= 21;
  loop assigns v, e, g;
*/
while (g>=3) {
      v = v+1;
      e = e+v;
      g = g-3;
  }

}
