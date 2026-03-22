int main1(){
  int w, p, wlhe;
  w=47;
  p=0;
  wlhe=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p <= w;
  loop invariant wlhe >= 0;
  loop invariant (p <= w/2) ==> (wlhe == 0);
  loop invariant (p > w/2) ==> (wlhe > 0);
  loop invariant (wlhe % 4 == 0);
  loop invariant (p <= 22) ==> (wlhe == 0);
  loop assigns p, wlhe;
*/
while (1) {
      if (!(p<w)) {
          break;
      }
      if (p>=w/2) {
          wlhe += 2;
      }
      p++;
      wlhe += wlhe;
  }
}