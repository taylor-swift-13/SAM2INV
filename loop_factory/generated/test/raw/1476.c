int main1(){
  int vo, yt, efh, ve, d;

  vo=1;
  yt=0;
  efh=vo;
  ve=5;
  d=0;

  while (1) {
      ve = (ve+efh)%4;
      yt = (yt + 1) % vo;
      d = d + efh;
      if (yt>=vo) {
          break;
      }
  }

}
