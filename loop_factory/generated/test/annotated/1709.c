int main1(int j){
  int z, pg, og, qd;
  z=j+11;
  pg=0;
  og=0;
  qd=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j == \at(j, Pre) && z == \at(j, Pre) + 11 && pg == 0 && (-8 <= qd) && (qd <= -8 + 4*og));
  loop invariant ((z >= 0) ==> (0 <= og && og <= z)) && ((z < 0) ==> (og == 0));
  loop assigns j, og, qd;
*/
while (1) {
      if (!(og<=z-1)) {
          break;
      }
      if (!(!(og>=z/2))) {
          qd += 4;
      }
      j = j + pg;
      og++;
  }
}