int main1(int a,int n){
  int l, e, g, v;

  l=21;
  e=0;
  g=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 5 * g;
  loop invariant e == 0;
  loop invariant 0 <= g && g <= l;
  loop invariant l == 21;
  loop invariant a == \at(a, Pre) && n == \at(n, Pre);
  loop invariant (1 + e) * v == 5 * g;
  loop invariant v == 5 * g && e == 0 && l == 21;
  loop invariant 0 <= g && g <= l && a == \at(a, Pre) && n == \at(n, Pre);
  loop invariant 5*g == (1+e)*v && e == 0 && l == 21;
  loop invariant g <= l && v >= 0 && a == \at(a, Pre) && n == \at(n, Pre);
  loop invariant 5*g == (1+e)*v;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v*(1+e) == 5*g;
  loop invariant e == 0 && 0 <= g && g <= l && a == \at(a, Pre) && n == \at(n, Pre) && l == 21;
  loop invariant 5*g == v*(1+e);
  loop invariant g <= l;
  loop invariant v >= 0;
  loop invariant e == 0 && l == 21 && g >= 0 && g <= l && v == 5 * g;
  loop assigns g, v;
*/
while (g<l) {
      v = v+5;
      g = g+1;
      g = g+e;
  }
/*@
  assert !(g<l) &&
         (v == 5 * g);
*/


}
