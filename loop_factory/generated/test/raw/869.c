int main1(int j){
  int q1qg, yct, qxi;

  q1qg=j+12;
  yct=0;
  qxi=0;

  while (1) {
      if (!(yct<=q1qg-1)) {
          break;
      }
      qxi += 1;
      j = j*4+(qxi%7)+1;
      yct = q1qg;
  }

}
