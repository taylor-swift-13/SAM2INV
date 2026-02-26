int main1(int b,int n){
  int k, v, z, s;

  k=21;
  v=0;
  z=-2;
  s=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 21;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant z >= -2;
  loop invariant (z + 2) % 8 == 0;
  loop invariant s >= 21;
  loop invariant (s + 16) % 37 == 0;
  loop invariant ( (z + 2) % 8 == 0 );
  loop invariant ( z >= -2 );
  loop invariant ( s >= 21 );
  loop invariant ( z <= s );
  loop invariant ( b == \at(b, Pre) );
  loop invariant ( n == \at(n, Pre) );
  loop assigns z, s;
*/
while (1) {
      z = z+8;
      s = s+8;
      s = s+s;
  }

}
