int main1(){
  int sr, vy, fh, rji, mp;

  sr=(1%24)+14;
  vy=sr;
  fh=19;
  rji=1;
  mp=0;

  while (fh>0&&rji<=sr) {
      if (!(fh<=rji)) {
          fh = 0;
      }
      else {
          fh = fh - rji;
      }
      mp += 1;
      vy += 1;
      rji++;
  }

}
