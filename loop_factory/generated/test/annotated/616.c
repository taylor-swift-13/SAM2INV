int main1(){
  int hwae, jdm, rnha;
  hwae=48;
  jdm=0;
  rnha=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hwae == 48;
  loop invariant 0 <= jdm;
  loop invariant jdm <= hwae;
  loop invariant jdm % 4 == 0;
  loop invariant rnha > 0;
  loop invariant rnha % 3 == 0;
  loop assigns jdm, rnha;
*/
for (; jdm<=hwae-4; jdm += 4) {
      rnha = rnha + rnha;
  }
}