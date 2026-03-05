int main1(){
  int z, ud, b7r, wc;
  z=49;
  ud=1;
  b7r=1;
  wc=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b7r == 1 + 3*(ud - 1);
  loop invariant wc == 4 + 3*(ud - 1);
  loop invariant ud <= z;
  loop invariant z == 49;
  loop invariant 1 <= ud;
  loop assigns ud, b7r, wc;
*/
for (; ud<z; ud++) {
      b7r = b7r + 3;
      wc = wc + 3;
  }
}