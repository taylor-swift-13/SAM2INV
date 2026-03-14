int main1(int f,int c){
  int rqd, bb, k, kn0, qt;

  rqd=38;
  bb=0;
  k=0;
  kn0=0;
  qt=12;

  while (1) {
      if (!(kn0<rqd)) {
          break;
      }
      k += f;
      kn0++;
      qt = qt*2;
      f = f+rqd-bb;
  }

  while (qt<kn0) {
      qt++;
      k += f;
      f = f+kn0-bb;
      f += bb;
  }

}
