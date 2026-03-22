int main1(){
  int vo, yt, efh, ve, d;
  vo=1;
  yt=0;
  efh=vo;
  ve=5;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (yt == 0);
  loop invariant ((ve % 4) == ((1 + d) % 4));
  loop invariant (d >= 0);
  loop invariant efh == vo;
  loop invariant 0 <= ve <= 5;
  loop invariant efh == 1;
  loop assigns ve, yt, d;
*/
while (1) {
      ve = (ve+efh)%4;
      yt = (yt + 1) % vo;
      d = d + efh;
      if (yt>=vo) {
          break;
      }
  }
}