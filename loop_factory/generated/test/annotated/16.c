int main1(int j,int r){
  int z, id2, r8;
  z=67;
  id2=0;
  r8=id2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r8 == 2 * id2;
  loop invariant j == \at(j, Pre) + id2 * (id2 + 3);
  loop invariant 0 <= id2;
  loop invariant id2 <= z;
  loop invariant z == 67;
  loop invariant r == \at(r, Pre);
  loop invariant j == \at(j, Pre) + id2 * id2 + 3 * id2;
  loop assigns id2, r8, j;
*/
while (1) {
      if (!(id2<z)) {
          break;
      }
      r8 += 2;
      id2 = id2 + 1;
      j += r8;
      j += 2;
  }
}