int main1(){
  int gh, fb82, ee, v0r;
  gh=1*2;
  fb82=(1%40)+2;
  ee=0;
  v0r=gh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gh == 2;
  loop invariant 0 <= ee;
  loop invariant ee <= 3;
  loop invariant 1 <= fb82;
  loop invariant fb82 <= 3;
  loop invariant v0r >= 2;
  loop assigns ee, fb82, v0r;
*/
while (1) {
      if (!(fb82!=ee)) {
          break;
      }
      ee = fb82;
      fb82 = (fb82+gh/fb82)/2;
      v0r = v0r+(fb82%4);
  }
}