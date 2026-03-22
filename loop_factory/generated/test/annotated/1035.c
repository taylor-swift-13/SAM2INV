int main1(){
  int uw, lx, xd5t, jec, oy;
  uw=(1%14)+4;
  lx=0;
  xd5t=1;
  jec=0;
  oy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jec == (xd5t - 1) * (xd5t - 1);
  loop invariant oy  == ((xd5t - 1) * xd5t * (2 * xd5t - 1)) / 6;
  loop invariant 1 <= xd5t <= uw + 1;
  loop assigns jec, xd5t, oy;
*/
while (xd5t<=uw) {
      jec = jec+2*xd5t-1;
      xd5t += 1;
      oy += jec;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= oy;
  loop assigns oy;
*/
while (1) {
      oy++;
      if (oy>=lx) {
          break;
      }
  }
}