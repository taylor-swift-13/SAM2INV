int main1(int a){
  int a5cs, olv, xyg, ec, zn2;
  a5cs=64;
  olv=0;
  xyg=a5cs;
  ec=0;
  zn2=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= olv;
  loop invariant olv <= a5cs;
  loop invariant xyg == a5cs - olv;
  loop invariant ec == olv*(olv+1)/2;
  loop invariant zn2 == 2*(olv+1);
  loop assigns olv, xyg, ec, zn2;
*/
while (1) {
      if (!(olv<a5cs&&xyg>0)) {
          break;
      }
      olv++;
      xyg = xyg - 1;
      ec = ec + olv;
      zn2 += 2;
  }
}