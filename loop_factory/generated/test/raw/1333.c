int main1(){
  int m, hn, hk, g5e;

  m=1+4;
  hn=(1%40)+2;
  hk=0;
  g5e=m;

  while (1) {
      if (!(hn!=hk)) {
          break;
      }
      hk = hn;
      g5e = g5e+(hk%2);
      hn = (hn+m/hn)/2;
  }

}
