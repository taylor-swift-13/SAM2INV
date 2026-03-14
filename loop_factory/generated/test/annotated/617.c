int main1(int y){
  int n1hk, yn, sukq, e, dnr;
  n1hk=39;
  yn=0;
  sukq=0;
  e=0;
  dnr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dnr == yn;
  loop invariant e == yn % 2;
  loop invariant sukq == yn / 2;
  loop invariant 0 <= yn <= n1hk;
  loop assigns e, dnr, sukq, yn;
*/
while (1) {
      if (!(yn<n1hk)) {
          break;
      }
      e += 1;
      dnr = dnr + 1;
      if (e>=2) {
          e -= 2;
          sukq += 1;
      }
      yn = yn + 1;
  }
}