int main1(int b,int n){
  int z, h, d;

  z=(b%37)+4;
  h=z;
  d=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant z == (\at(b, Pre) % 37) + 4;
  loop invariant h == z;
  loop invariant d >= -6;
  loop invariant b == \at(b, Pre) &&
                   n == \at(n, Pre) &&
                   h == z &&
                   z == (\at(b, Pre) % 37) + 4;

  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant z == (b % 37) + 4;

  loop invariant (n >= 6) ==> ((-6 <= d) && (d <= 0));
  loop invariant h == z && z == (\at(b, Pre) % 37) + 4 && b == \at(b, Pre);
  loop invariant n == \at(n, Pre) && d >= -6;

  loop invariant h <= 40;

  loop assigns d;
*/
while (h-2>=0) {
      d = d+4;
      if (h+6<=n+z) {
          d = d-d;
      }
      else {
          d = d+1;
      }
  }

}
