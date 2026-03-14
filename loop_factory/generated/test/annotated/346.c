int main1(){
  int hnz, vs, nbs7, o1f;
  hnz=1;
  vs=4;
  nbs7=0;
  o1f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o1f == nbs7 * hnz;
  loop invariant vs == 4 + nbs7;
  loop invariant nbs7 <= hnz;
  loop assigns vs, nbs7, o1f;
*/
while (nbs7<hnz) {
      vs += 1;
      nbs7 = nbs7 + 1;
      o1f += hnz;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o1f == (1 + vs) * nbs7 - 5;
  loop invariant hnz == 1;
  loop invariant o1f == 1 + (nbs7 - 1) * (vs + 1);
  loop invariant nbs7 <= hnz;
  loop invariant vs == 5;
  loop assigns nbs7, o1f;
*/
while (nbs7<hnz) {
      o1f++;
      nbs7 = nbs7 + 1;
      o1f = o1f + vs;
  }
}