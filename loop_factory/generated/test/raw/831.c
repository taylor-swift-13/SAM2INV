int main1(int g,int n){
  int gdn, ycm, j9g, dur, os, q9;

  gdn=74;
  ycm=n;
  j9g=n;
  dur=0;
  os=(n%6)+2;
  q9=0;

  while (1) {
      if (!(dur<=gdn-1)) {
          break;
      }
      ycm = ycm*os+n;
      dur++;
      j9g = j9g*os;
      os = os+(j9g%2);
      q9 += 1;
  }

}
