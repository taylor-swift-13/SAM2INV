int main1(int a,int b,int n,int q){
  int r, g, v, p, z, u;

  r=(a%29)+7;
  g=0;
  v=6;
  p=b;
  z=b;
  u=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g >= 0;
  loop invariant v == 6 + g + (g * (g - 1)) / 2;
  loop invariant z == b * (g + 1) + (g * (g - 1)) / 2;
  loop invariant p == b;
  loop invariant (g == 0) ==> (u == 0);


  loop invariant p == \at(b,Pre);

  loop invariant z == b*(g+1) + g*(g-1)/2;

  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant a == \at(a, Pre) &&
                   b == \at(b, Pre) &&
                   n == \at(n, Pre);
  loop invariant v >= 6;
  loop assigns u, v, z, g;
*/
while (1) {
      u = v+p+z;
      v = v+1;
      z = z+p;
      z = z+g;
      v = v+g;
      g = g+1;
  }

}
