int main1(){
  int ma, lg, lr, wim;
  ma=80;
  lg=0;
  lr=lg;
  wim=ma;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ma == 80;
  loop invariant lg <= ma;
  loop invariant wim >= 80;
  loop invariant lr == wim*wim - ma*ma;
  loop invariant lg == ma * (wim - ma);
  loop assigns lr, wim, lg;
*/
while (1) {
      if (!(lg < ma)) {
          break;
      }
      lr--;
      wim = wim + 1;
      lr = lr+wim+wim;
      lg = ma;
  }
}