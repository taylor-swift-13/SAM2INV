int main1(int q,int b){
  int ti, rp, v, wq;
  ti=73;
  rp=0;
  v=b;
  wq=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wq == -6 + rp * ti - rp * (rp + 1) / 2;
  loop invariant 0 <= rp <= ti;
  loop invariant ((rp == 0) ==> (v == b)) && ((rp > 0) ==> (v == ti - rp));
  loop assigns rp, v, wq;
*/
while (rp<=ti-1) {
      rp++;
      v = ti-rp;
      wq += v;
  }
}