int main1(){
  int smk, zf, jpl, owp, d2;
  smk=27;
  zf=smk+6;
  jpl=(1%40)+2;
  owp=0;
  d2=zf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d2 % 3 == 0;
  loop invariant owp >= 0;
  loop invariant jpl > 0;
  loop invariant smk == 27;
  loop invariant d2 >= 33;
  loop assigns owp, d2, jpl;
*/
while (1) {
      if (!(jpl!=owp)) {
          break;
      }
      owp = jpl;
      d2 += owp;
      jpl = (jpl+smk/jpl)/2;
      d2 = d2*3;
  }
}