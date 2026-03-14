int main1(){
  int bdm, uo, u, sxtg, c;
  bdm=0;
  uo=0;
  u=(1%28)+10;
  sxtg=bdm;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sxtg == bdm * uo;
  loop invariant bdm == 0;
  loop invariant u + ((uo)*(uo-1))/2 == (1%28 + 10);
  loop assigns sxtg, u, uo;
*/
while (u>uo) {
      u -= uo;
      sxtg = (bdm)+(sxtg);
      uo = uo + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sxtg + bdm == c;
  loop invariant bdm >= 0;
  loop invariant c >= 0;
  loop invariant sxtg <= 0;
  loop assigns sxtg, c, bdm;
*/
while (sxtg>c) {
      sxtg = sxtg - c;
      c = (1)+(c);
      bdm = bdm + c;
  }
}