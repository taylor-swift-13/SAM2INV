int main1(){
  int ts, w, xch;
  ts=(1%6)+12;
  w=2;
  xch=ts;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ts == 13;
  loop invariant w <= ts;
  loop invariant (xch + 2) % (ts + 2) == 0;
  loop invariant w >= 2;
  loop invariant xch >= ts;
  loop invariant xch >= 2*w;
  loop assigns w, xch;
*/
while (w<ts) {
      xch += 1;
      w += 1;
      xch = xch + xch;
  }
}