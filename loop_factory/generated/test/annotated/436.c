int main1(){
  int ftaf, tmb, l4i, i1, z;
  ftaf=1;
  tmb=3;
  l4i=1;
  i1=0;
  z=tmb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z - (l4i - 1) * (ftaf - tmb) == 3;
  loop invariant i1 == ((l4i - 1) * l4i * (2 * l4i - 1)) / 6;
  loop invariant z == tmb + (ftaf - tmb) * (l4i - 1);
  loop invariant (1 <= l4i);
  loop invariant (l4i <= ftaf + 1);
  loop assigns i1, l4i, z;
*/
while (1) {
      if (!(l4i<=ftaf)) {
          break;
      }
      i1 = i1+l4i*l4i;
      l4i++;
      z = z+ftaf-tmb;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= l4i <= ftaf + 1;
  loop invariant l4i >= ftaf;
  loop assigns l4i;
*/
while (1) {
      l4i++;
      if (l4i>=ftaf) {
          break;
      }
  }
}