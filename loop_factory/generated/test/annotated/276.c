int main1(){
  int qk, lrg, hqk, akt, eo5, mjqx;
  qk=1*2;
  lrg=0;
  hqk=27;
  akt=0;
  eo5=1;
  mjqx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hqk + akt == 27;
  loop invariant 0 <= lrg <= qk;
  loop invariant eo5 == lrg + 1;
  loop invariant akt <= lrg*(lrg+1)/2;
  loop invariant mjqx <= eo5;
  loop invariant mjqx <= hqk;
  loop assigns mjqx, lrg, hqk, akt, eo5;
*/
while (hqk>0&&lrg<qk) {
      if (hqk<=eo5) {
          mjqx = hqk;
      }
      else {
          mjqx = eo5;
      }
      lrg++;
      hqk -= mjqx;
      akt += mjqx;
      eo5++;
  }
}