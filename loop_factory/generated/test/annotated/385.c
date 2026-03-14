int main1(){
  int c, tas, jnd, ss;
  c=1+6;
  tas=-4;
  jnd=-4;
  ss=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ss == (tas*tas + tas)/2 - 1;
  loop invariant tas >= -4;
  loop invariant tas <= c;
  loop invariant (jnd + tas == c + 1) || (jnd == -4 && tas == -4 && c == 1 + 6);
  loop assigns jnd, tas, ss;
*/
while (tas<=c-1) {
      jnd = c-tas;
      tas++;
      ss += tas;
  }
}