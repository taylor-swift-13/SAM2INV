int main1(){
  int hj, fs, v68, ij;
  hj=1;
  fs=0;
  v68=2;
  ij=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hj == 1;
  loop invariant (ij == 1) || (ij == -1);
  loop invariant v68 <= (2 + fs);
  loop invariant (v68 + fs) % 2 == 0;
  loop invariant 0 <= fs <= hj;
  loop invariant 2 <= v68 <= 12;
  loop assigns fs, ij, v68;
*/
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