int main1(){
  int yk, bpun, q05, om, ljua;
  yk=128;
  bpun=0;
  q05=yk;
  om=bpun;
  ljua=yk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant om == 0;
  loop invariant q05 == 128;
  loop invariant 0 <= bpun <= yk;
  loop invariant ljua >= 128;
  loop invariant yk == 128;
  loop assigns bpun, q05, om, ljua;
*/
while (1) {
      if (!(bpun < yk)) {
          break;
      }
      q05 = q05+(om%7);
      bpun += 1;
      om = om*3+(om%6)+0;
      ljua = ljua+(ljua%7);
  }
}