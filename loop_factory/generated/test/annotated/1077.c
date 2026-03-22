int main1(){
  int ct, sf, ze, jj, vdnt;
  ct=1-2;
  sf=0;
  ze=0;
  jj=0;
  vdnt=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vdnt + jj == 6;
  loop invariant ze == jj;
  loop invariant ct == -1;
  loop invariant sf >= 0;
  loop invariant 0 <= vdnt <= 6;
  loop assigns sf, ze, jj, vdnt;
*/
while (vdnt>=1) {
      sf = sf+1*1;
      ze = ze+1*1;
      jj = jj+1*1;
      vdnt--;
      sf = sf*4+5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sf >= 0;
  loop invariant vdnt >= 0;
  loop invariant ze >= 0;
  loop invariant ct <= -1;
  loop assigns vdnt, sf, ct, ze;
*/
while (1) {
      if (!(ct>0)) {
          break;
      }
      vdnt = vdnt+1*1;
      sf = sf+1*1;
      ct = (ct)+(-(1));
      ze = ze+1*1;
      vdnt = vdnt*2;
  }
}