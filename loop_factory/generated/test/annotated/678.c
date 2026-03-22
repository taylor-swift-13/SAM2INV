int main1(){
  int o2, q0t, ln, pr, ug9;
  o2=1*5;
  q0t=o2;
  ln=(1%40)+2;
  pr=0;
  ug9=q0t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ug9 - ln == 2;
  loop invariant o2 == 5;
  loop invariant ln > 0;
  loop invariant pr >= 0;
  loop assigns pr, ln, ug9;
*/
while (ln!=pr) {
      pr = ln;
      ln = (ln+o2/ln)/2;
      ug9 = (ug9+ln)+(-(pr));
  }
}