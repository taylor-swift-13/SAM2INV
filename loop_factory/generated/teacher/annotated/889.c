int main1(int b,int n){
  int r, z, u;

  r=(n%34)+11;
  z=r;
  u=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (\at(n, Pre) % 34) + 11;
  loop invariant z <= r;
  loop invariant u >= r;
  loop invariant (u - z) % 4 == 0;
  loop invariant u - z >= 0;
  loop invariant z % 4 == r % 4;
  loop invariant r == \at(n, Pre) % 34 + 11;
  loop invariant u % 4 == r % 4;
  loop invariant (r - z) % 4 == 0;
  loop invariant (r - z) >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant u + z <= 2*r &&
                   z <= r;
  loop invariant r == \at(n, Pre) % 34 + 11 && n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant u >= z && z <= r && u >= r && (u - z) % 4 == 0 && z % 4 == r % 4;
  loop invariant r == (\at(n, Pre) % 34) + 11 && n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant z % 4 == r % 4 && z <= r && u >= r && (u - r) % 4 == 0;
  loop invariant n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant (u + z) <= 2 * r && ((2 * r - (u + z)) % 4) == 0;
  loop invariant r == (n % 34) + 11;

  loop invariant (u - r) % 4 == 0;

  loop invariant r >= z && (r - z) % 4 == 0 && u >= r;
  loop assigns u, z;
*/
while (z>3) {
      if (z+5<=u+r) {
          u = u+4;
      }
      z = z-4;
  }

}
