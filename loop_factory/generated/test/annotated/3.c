int main1(){
  int g3;
  g3=(1%15)+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g3 >= 0;
  loop invariant 0 <= 4 - g3;
  loop assigns g3;
*/
while (g3!=0) {
      g3 -= 1;
  }
}