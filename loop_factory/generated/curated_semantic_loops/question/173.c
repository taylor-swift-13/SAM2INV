int main1(int m,int q){
  int z, j, f, v;

  z=(q%27)+8;
  j=0;
  f=m;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j<z) {
      f = f*2;
      j = j+1;
  }
/*@
  assert !(j<z) &&
         (0 <= j);
*/

}
