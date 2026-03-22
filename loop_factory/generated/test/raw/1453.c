int main1(){
  int w, p, wlhe;

  w=47;
  p=0;
  wlhe=0;

  while (1) {
      if (!(p<w)) {
          break;
      }
      if (p>=w/2) {
          wlhe += 2;
      }
      p++;
      wlhe += wlhe;
  }

}
