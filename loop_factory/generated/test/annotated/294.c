int main1(){
  int kcn, q73, cceh, xr0, yf, n6o;
  kcn=1;
  q73=0;
  cceh=0;
  xr0=kcn;
  yf=q73;
  n6o=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (yf == (cceh * (cceh + 1)) / 2);
  loop invariant xr0 == kcn - cceh;
  loop invariant 0 <= cceh <= kcn;
  loop assigns cceh, yf, xr0;
*/
while (cceh<=kcn-1) {
      cceh++;
      yf = yf + cceh;
      xr0 = (kcn)+(-(cceh));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yf <= kcn - n6o;
  loop invariant 0 <= q73 - n6o <= 8;
  loop assigns n6o, yf;
*/
while (1) {
      if (!(n6o<q73)) {
          break;
      }
      n6o += 1;
      yf = (q73)+(-(n6o));
      yf += kcn;
  }
}