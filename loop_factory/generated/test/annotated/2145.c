int main1(int s){
  int x4mk, z, y83, jm, a;
  x4mk=73;
  z=0;
  y83=0;
  jm=0;
  a=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z;
  loop invariant z <= x4mk;
  loop invariant x4mk == 73;
  loop invariant (z == 0) || ( ((z - 1) % 2 == 0) ==> (a - jm == y83) );
  loop invariant (z == 0) || ( ((z - 1) % 2 == 1) ==> (a == 2 * jm) );
  loop invariant s == \at(s, Pre);
  loop invariant (z == 0) ==> (y83 == 0 && jm == 0 && a == \at(s, Pre));
  loop assigns a, y83, jm, z;
*/
while (1) {
      if (!(z < x4mk)) {
          break;
      }
      y83 = (1 - (z % 2)) * a + (z % 2) * y83;
      jm = (z % 2) * a + (1 - (z % 2)) * jm;
      a = a + jm;
      z += 1;
  }
}