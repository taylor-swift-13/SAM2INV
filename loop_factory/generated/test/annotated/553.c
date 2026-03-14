int main1(){
  int ti, p5, ts, fxn, qogc;
  ti=1;
  p5=ti;
  ts=0;
  fxn=ti;
  qogc=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fxn == ti - ts;
  loop invariant p5 == ti;
  loop invariant qogc == 5 + ts;
  loop invariant ts <= ti;
  loop invariant fxn == 1 - ts;
  loop invariant qogc == 5 + (ti - p5 + 1) * ts;
  loop invariant fxn >= 0;
  loop invariant 0 <= ts;
  loop assigns fxn, ts, qogc;
*/
while (ts<ti&&fxn>0) {
      fxn = fxn - 1;
      ts = ts + 1;
      qogc = qogc+ti-p5;
      qogc = (1)+(qogc);
  }
}