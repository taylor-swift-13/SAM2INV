int main1(int n,int q){
  int b, g, u, a;

  b=q+14;
  g=1;
  u=b;
  a=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(q, Pre) + 14;
  loop invariant u >= b;
  loop invariant g >= 1;
  loop invariant (g == 1) || (g <= b);
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (g == 1 || g % 3 == 0);
  loop invariant g >= 1 && (g == 1 || g % 3 == 0) && b == \at(q, Pre) + 14;

  loop invariant q == \at(q, Pre) && n == \at(n, Pre);
  loop invariant b == \at(q, Pre) + 14 && (g == 1 || g % 3 == 0);

  loop invariant g > 0;
  loop invariant g == 1 || g % 3 == 0;
  loop invariant b >= 0 ==> u >= 0;
  loop invariant u >= b && g >= 1 && n == \at(n, Pre);
  loop assigns u, g;
*/
while (g<=b/3) {
      u = u*u+u;
      g = g*3;
  }
/*@
  assert !(g<=b/3) &&
         (b == \at(q, Pre) + 14);
*/


}
