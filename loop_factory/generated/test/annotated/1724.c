int main1(){
  int z, y6ai, e3i, j;
  z=1-2;
  y6ai=0;
  e3i=z - y6ai;
  j=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e3i == z - y6ai;
  loop invariant j - z*y6ai == z;
  loop invariant y6ai >= 0;
  loop invariant j == z * y6ai - 1;
  loop invariant j == z * (y6ai + 1);
  loop assigns y6ai, j, e3i;
*/
while (1) {
      if (!(y6ai < z)) {
          break;
      }
      y6ai += 1;
      j += z;
      e3i = (z)+(-(y6ai));
  }
}