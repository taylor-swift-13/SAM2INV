int main1(){
  int ie;
  ie=-2861;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ie % 2861) == 0;
  loop invariant ie <= -2861 && (ie == -2861 || ie % 2 == 0);
  loop assigns ie;
*/
while (ie<=-7) {
      ie = ie+ie-2;
      ie += 2;
  }
}