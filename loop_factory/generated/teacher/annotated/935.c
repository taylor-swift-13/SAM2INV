int main1(int b,int n){
  int h, p, f, g;

  h=b;
  p=0;
  f=4;
  g=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g >= b && f >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant g >= \at(b, Pre);
  loop invariant (f == g*g) || (g == \at(b, Pre) && f == 4);
  loop invariant h == b;
  loop invariant g >= h;
  loop invariant f >= 0;
  loop invariant n == \at(n, Pre) && g >= h && f >= 0;
  loop invariant g >= b;
  loop invariant (f == 4) || (f == g*g);
  loop invariant (g > \at(b,Pre)) ==> (f == g*g);
  loop invariant g >= \at(b,Pre);
  loop invariant h == b && b == \at(b, Pre) && n == \at(n, Pre) && f >= 0;
  loop invariant (f == g*g) || (g == b && f == 4);
  loop invariant (g > \at(b, Pre)) ==> (f == g*g);
  loop invariant (g == \at(b, Pre)) ==> (f == 4);
  loop invariant b == \at(b, Pre);
  loop assigns g, f;
*/
while (1) {
      g = g+1;
      f = g*g;
  }

}
