int main1(){
  int hj, fs, v68, ij;
  hj=1;
  fs=0;
  v68=2;
  ij=1;
  /* >>> LOOP INVARIANT TO FILL <<< */

for (; fs<hj; fs++) {
      if (!(v68<12)) {
          ij = -1;
      }
      if (v68<=2) {
          ij = 1;
      }
      v68 = v68 + ij;
  }
/*@
  assert !(fs<hj) &&
         (hj == 1);
*/

}