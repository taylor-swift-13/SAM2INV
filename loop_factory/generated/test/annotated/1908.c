int main1(int g,int n){
  int g4cq, fk, nmd, w94, cw, gw, o, wfwj;
  g4cq=5;
  fk=0;
  nmd=0;
  w94=0;
  cw=0;
  gw=0;
  o=0;
  wfwj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cw == fk;
  loop invariant gw == n * (fk / 3);
  loop invariant wfwj == fk + ((fk + 1) / 2);
  loop invariant 0 <= fk <= g4cq;
  loop assigns nmd, w94, gw, o, cw, fk, g, wfwj;
*/
while (fk < g4cq) {
      if ((fk % 3) == 0) {
          nmd += n;
      }
      if ((fk % 3) == 1) {
          w94 = w94+2*n;
      }
      if ((fk % 3) == 2) {
          gw += n;
      }
      else {
          o = o + g;
      }
      cw += 1;
      fk += 1;
      g += gw;
      wfwj = wfwj+(fk%2);
      g -= 1;
      wfwj += 1;
  }
}