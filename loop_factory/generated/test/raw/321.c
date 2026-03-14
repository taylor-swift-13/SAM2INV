int main1(int r,int g){
  int w, ke, ptuo, yqd;

  w=r*5;
  ke=3;
  ptuo=0;
  yqd=0;

  while (yqd<w) {
      ptuo += r;
      yqd++;
  }

  while (1) {
      if (!(ke<yqd)) {
          break;
      }
      w += r;
      ke++;
  }

}
