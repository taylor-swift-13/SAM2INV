int main1(int b,int p){
  int e, t, z;

  e=38;
  t=3;
  z=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre) && p == \at(p, Pre) && e == 38 && t == 3;
  loop invariant z >= t && (z - t) % 5 == 0;
  loop invariant z % 5 == 3;
  loop invariant z >= 3;
  loop invariant t == 3;
  loop invariant e == 38;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant e == 38 && t == 3 && z >= 3 && z % 5 == 3;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z >= t;
  loop invariant (z - t) % 5 == 0;
  loop invariant (z - 3) % 5 == 0;
  loop assigns z;
*/
while (1) {
      z = z+4;
      if ((t%4)==0) {
          z = z+1;
      }
      else {
          z = z+1;
      }
  }

}
