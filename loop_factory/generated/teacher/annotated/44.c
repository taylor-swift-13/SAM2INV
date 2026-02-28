int main1(int p,int q){
  int x, z, s;

  x=40;
  z=0;
  s=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 0;
  loop invariant 0 <= z && z <= x;
  loop invariant x == 40;
  loop invariant p == \at(p, Pre);
  loop invariant z <= x;
  loop invariant q == \at(q, Pre);
  loop invariant z >= 0;
  loop assigns s, z;
*/
while (z<x) {
      s = p;
      s = s-s;
      z = z+1;
  }

}
