int main1(int b,int q){
  int r, z, t;

  r=13;
  z=0;
  t=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 0;
  loop invariant t == b + z*(z - 1)/2 + (z + 3)/4;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t == \at(b, Pre) + z*(z-1)/2 + (z + 3)/4;
  loop invariant r == 13;
  loop invariant t >= b;
  loop invariant (z == 0) ==> (t == b);
  loop invariant (z > 0) ==> (t == b + (z*(z-1))/2 + ((z-1)/4) + 1);
  loop invariant t == \at(b,Pre) + (z * (z - 1)) / 2 + (z + 3) / 4;
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant b == \at(b,Pre) && q == \at(q,Pre) && r == 13;
  loop invariant t >= \at(b,Pre) + (z*(z-1))/2 && z >= 0;
  loop invariant t >= \at(b, Pre);
  loop invariant t >= \at(b, Pre) + z*(z-1)/2;
  loop invariant t - z*(z-1)/2 - (z+3)/4 == b && z >= 0;
  loop invariant b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant t - \at(b, Pre) >= z*(z-1)/2;
  loop invariant z >= 0 && r == 13 && t >= \at(b, Pre);
  loop assigns t, z;
*/
while (1) {
      t = t+z;
      if ((z%4)==0) {
          t = t+1;
      }
      z = z+1;
  }

}
