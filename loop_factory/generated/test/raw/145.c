int main1(){
  int cg, jn, i, yez0, v4i, kp, wv4;

  cg=1+10;
  jn=0;
  i=2;
  yez0=2;
  v4i=0;
  kp=6;
  wv4=0;

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
