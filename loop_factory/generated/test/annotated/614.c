int main1(){
  int v, kotc;
  v=1;
  kotc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 1;
  loop invariant (kotc % 2) == 0;
  loop invariant kotc >= 0;
  loop assigns kotc;
*/
for (; kotc<=v-2; kotc += 2) {
  }
}