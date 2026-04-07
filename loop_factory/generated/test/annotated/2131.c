int main1(){
  int rr, dm, x2vq, fwq;
  rr=1+22;
  dm=0;
  x2vq=dm;
  fwq=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (rr == dm) || (rr == 1+22);
  loop invariant dm == 0;
  loop invariant fwq == 2;
  loop invariant 0 <= x2vq;
  loop invariant x2vq <= 1+22;
  loop invariant (rr == dm) || (rr >= (dm + 1));
  loop invariant x2vq >= dm;
  loop assigns x2vq, fwq, rr;
*/
while (1) {
      if (!(dm+1<=rr)) {
          break;
      }
      if (x2vq+3<=rr) {
          x2vq = x2vq + 3;
      }
      else {
          x2vq = rr;
      }
      fwq = fwq + dm;
      rr = (dm+1)-1;
  }
}