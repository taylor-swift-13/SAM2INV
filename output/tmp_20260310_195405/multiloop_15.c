int main1(int k){
  int i, ur, ldo, aud, za;
  i=54;
  ur=0;
  ldo=0;
  aud=0;
  za=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant za == i + ur * ldo;
  loop invariant i == 54;
  loop invariant ldo <= i;
  loop invariant 2*aud == ldo*(ldo - 1);
  loop invariant za == i;
  loop assigns aud, za, ldo;
*/
while (ldo<i) {
      aud = aud + ldo;
      za = za + ur;
      ldo++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant za == 54;
  loop assigns aud;
*/
while (aud<za) {
      aud += 1;
  }
/*@
  assert !(aud<za) &&
         (za == i + ur * ldo);
*/

}