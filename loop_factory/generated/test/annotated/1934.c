int main1(int d){
  int tw, vx, nbu, bpr;
  tw=d+17;
  vx=0;
  nbu=0;
  bpr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tw == d + 17;
  loop invariant vx >= 0;
  loop invariant (d != 0) ==> (vx == nbu * d + bpr);
  loop invariant (tw >= 0) ==> (vx <= tw);
  loop invariant (d != 0) ==> (0 <= bpr);
  loop invariant (d > 0) ==> (0 <= bpr && bpr < d && nbu >= 0);
  loop assigns vx, bpr, nbu;
*/
while (1) {
      if (!(vx < tw)) {
          break;
      }
      vx++;
      bpr = vx % d;
      nbu = vx / d;
  }
}