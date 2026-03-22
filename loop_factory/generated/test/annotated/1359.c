int main1(){
  int lwl, z, ne;
  lwl=1;
  z=0;
  ne=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lwl == 1;
  loop invariant z >= 0;
  loop invariant z <= lwl;
  loop invariant ne == 13 * (z + 1);
  loop assigns z, ne;
*/
for (; z<lwl; z += 1) {
      ne = ne*2;
  }
}