int main1(int n,int q){
  int z, v, j, i;

  z=44;
  v=0;
  j=5;
  i=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 44;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j <= z;
  loop invariant j >= 5;
  loop invariant 5 <= j;
  loop invariant z - j >= 0;
  loop assigns j;
*/
while (j<z) {
      if (j<z) {
          j = j+1;
      }
  }

}
