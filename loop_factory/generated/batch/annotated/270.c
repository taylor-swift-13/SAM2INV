int main1(int k,int m){
  int l, y, g, z;

  l=25;
  y=l+6;
  g=-3;
  z=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= l;
  loop invariant g >= -3;
  loop invariant g <= z + 5;
  loop invariant l == 25;
  loop invariant g <= z;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g < z;
  loop invariant (z + 6) % 31 == 0;

  loop assigns g, z;
*/
while (g<l) {
      if (g<l) {
          g = g+1;
      }
      g = g+z;
      z = z+z;
      z = z+6;
  }

}
