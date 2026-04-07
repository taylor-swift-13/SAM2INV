int main1(){
  int cb, hu, v, lt, kc, fwt;
  cb=1+7;
  hu=1;
  v=hu;
  lt=1;
  kc=hu;
  fwt=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v * (fwt - 1) == fwt * lt - 1;
  loop invariant lt > 0;
  loop invariant v >= 0;
  loop invariant 1 <= kc <= cb;
  loop invariant v >= lt;
  loop assigns v, lt, kc;
*/
while (1) {
      if (kc>=cb) {
          break;
      }
      v = v*fwt+1;
      lt = lt*fwt;
      kc += 1;
  }
}