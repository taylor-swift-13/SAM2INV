int main1(){
  int gw, ym, iaq, l7, ep, vh, tfp;
  gw=51;
  ym=0;
  iaq=8;
  l7=8;
  ep=0;
  vh=8;
  tfp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ym <= gw;
  loop invariant 0 <= iaq <= vh;
  loop invariant tfp == ym;
  loop invariant 0 <= ep <= tfp;
  loop invariant l7 >= 8;
  loop assigns ep, iaq, l7, tfp, ym;
*/
while (ym<=gw-1) {
      if (!(!(ym%3==0))) {
          if (iaq>0) {
              iaq--;
              ep = ep + 1;
          }
      }
      else {
          if (iaq<vh) {
              iaq = iaq + 1;
              l7++;
          }
      }
      tfp = tfp + 1;
      ym += 1;
  }
}