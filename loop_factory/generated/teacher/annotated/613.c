int main1(int a,int n){
  int b, g, k, z;

  b=(n%32)+8;
  g=2;
  k=g;
  z=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 2;
  loop invariant z >= 2;
  loop invariant (z - 2) % 2 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == ((\at(n, Pre) % 32) + 8);
  loop invariant b == (\at(n, Pre) % 32) + 8;
  loop invariant b == (n % 32) + 8;
  loop assigns z;
*/
while (1) {
      z = z+k;
  }

}
