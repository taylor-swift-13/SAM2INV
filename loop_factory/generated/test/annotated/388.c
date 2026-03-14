int main1(){
  int gq, g, rk, h4;
  gq=1+10;
  g=0;
  rk=gq;
  h4=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (g == 0) ==> (rk == gq);
  loop invariant (g != 0) ==> (rk == gq + 1);
  loop invariant 0 <= g <= gq;
  loop invariant 0 <= rk - gq <= h4;
  loop invariant (g <= gq) && ((g == 0) || (g == gq)) && (rk >= gq);
  loop invariant ((rk == gq) || (rk == gq + 1));
  loop assigns g, rk;
*/
while (1) {
      if (!(g<gq)) {
          break;
      }
      if (!(!(g<gq/2))) {
          rk += 1;
      }
      else {
          rk += h4;
      }
      g = gq;
  }
}