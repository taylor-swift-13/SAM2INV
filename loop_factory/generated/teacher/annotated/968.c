int main1(int n,int q){
  int h, t, z;

  h=12;
  t=2;
  z=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= \at(n,Pre);
  loop invariant ((z - \at(n,Pre)) % 3) == 0;
  loop invariant t == 2;
  loop invariant h == 12;
  loop invariant n == \at(n,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant h == 12 && t == 2 && n == \at(n,Pre) && q == \at(q,Pre);
  loop invariant z >= \at(n,Pre) && (z - \at(n,Pre)) % 3 == 0;
  loop invariant h == 12 && t == 2 && n == \at(n, Pre) && z >= \at(n, Pre) && (z - \at(n, Pre)) % 3 == 0;
  loop invariant t % 5 != 0;
  loop invariant z >= n && (z - n) % 3 == 0;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre) && t == 2;

  loop invariant z >= n;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (z - \at(n, Pre)) % 3 == 0;
  loop invariant (z - \at(n, Pre)) % 3 == 0 && z >= \at(n, Pre);
  loop invariant t == 2 && h == 12 && n == \at(n, Pre) && q == \at(q, Pre) && (t % 5) != 0;
  loop invariant (z - n) % 3 == 0;
  loop invariant z >= \at(n, Pre);
  loop invariant ((z - \at(n, Pre)) % 3) == 0;
  loop assigns z;
*/
while (1) {
      z = z+3;
      if ((t%5)==0) {
          z = z-z;
      }
  }

}
