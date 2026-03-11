int main1(int b,int k){
  int v, o, j, z;

  v=b;
  o=v;
  j=o;
  z=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j<v) {
      if (j<v) {
          j = j+1;
      }
      j = j+1;
  }
/*@
  assert !(j<v) &&
         (v == b);
*/

}
