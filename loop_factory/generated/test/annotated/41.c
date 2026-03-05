int main1(){
  int ya, u2, tjg;
  ya=(1%32)+5;
  u2=0;
  tjg=ya;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tjg >= ya;
  loop invariant ya == 6;
  loop invariant u2 == 0;
  loop invariant tjg % 4 == 2;
  loop assigns tjg;
*/
while (u2<ya) {
      tjg++;
      tjg = tjg + tjg;
  }
}