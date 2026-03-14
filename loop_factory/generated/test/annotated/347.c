int main1(int h,int y){
  int yq, s0, hd, w, ed;
  yq=(y%30)+20;
  s0=yq;
  hd=0;
  w=0;
  ed=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ed == 8 + w * s0;
  loop invariant hd == w * h;
  loop invariant s0 == yq;
  loop invariant w >= 0;
  loop assigns ed, hd, w;
*/
while (w<yq) {
      hd += h;
      ed = ed + s0;
      w += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w;
  loop assigns ed, yq, w;
*/
while (w<s0) {
      ed = ed+yq*w;
      yq += 2;
      w = s0;
  }
}