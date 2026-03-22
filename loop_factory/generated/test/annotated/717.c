int main1(){
  int hlt, ckx, s2, q6;
  hlt=(1%23)+9;
  ckx=(1%40)+2;
  s2=0;
  q6=hlt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ckx == 3;
  loop invariant q6 == hlt + (ckx - 3);
  loop invariant s2 <= ckx;
  loop invariant (q6 - ckx) == 7;
  loop assigns s2, ckx, q6;
*/
while (ckx!=s2) {
      s2 = ckx;
      ckx = (ckx+hlt/ckx)/2;
      q6 = q6+ckx-s2;
  }
}