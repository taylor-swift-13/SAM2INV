int main1(){
  int o, nyk;
  o=1+4;
  nyk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 1 + 4;
  loop invariant nyk <= 2*o + 1 && (nyk == 0 || nyk % 2 == 1);
  loop assigns nyk;
*/
while (nyk<=o) {
      nyk = 2*nyk;
      nyk += 1;
  }
}