int main1(){
  int hxp, qy, sf, so;
  hxp=1+20;
  qy=0;
  sf=0;
  so=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant so == 0;
  loop invariant hxp == 1 + 20;
  loop invariant sf <= 1;
  loop invariant 0 <= qy <= hxp;
  loop invariant sf >= 0;
  loop assigns qy, sf, so;
*/
while (sf>0&&qy<hxp) {
      if (sf<sf) {
          sf = sf;
      }
      else {
          sf = sf;
      }
      sf = sf - sf;
      so = so + sf;
      sf++;
      qy = qy + 1;
  }
}