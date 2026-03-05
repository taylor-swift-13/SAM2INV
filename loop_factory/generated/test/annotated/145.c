int main1(){
  int cg, jn, i, yez0, v4i, kp, wv4;
  cg=1+10;
  jn=0;
  i=2;
  yez0=2;
  v4i=0;
  kp=6;
  wv4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jn == wv4;
  loop invariant 0 <= jn;
  loop invariant 0 <= v4i;
  loop invariant i <= kp;
  loop invariant kp >= 6;
  loop invariant i >= 0;
  loop invariant v4i <= wv4;
  loop invariant kp >= v4i;
  loop invariant wv4 <= cg;
  loop invariant yez0 >= 2;
  loop assigns i, v4i, yez0, wv4, jn, kp;
*/
while (jn<cg) {
      if (jn%3==0) {
          if (i>0) {
              i--;
              v4i += 1;
          }
      }
      else {
          if (i<kp) {
              i = i + 1;
              yez0 += 1;
          }
      }
      wv4++;
      jn = jn + 1;
      kp = kp + v4i;
  }
}