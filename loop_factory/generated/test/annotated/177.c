int main1(){
  int wg, t;
  wg=53;
  t=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wg == 53;
  loop invariant t % 3 == 1;
  loop invariant t <= wg + 2;
  loop invariant t >= 1;
  loop assigns t;
*/
while (t<=wg) {
      t += 1;
      t += 2;
  }
}