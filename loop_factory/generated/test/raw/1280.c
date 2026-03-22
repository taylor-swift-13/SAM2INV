int main1(int j){
  int i5s, e, v0, v, yf, aaf;

  i5s=j*2;
  e=0;
  v0=0;
  v=0;
  yf=0;
  aaf=7;

  while (e<i5s) {
      v = e%5;
      if (!(!(e>=aaf))) {
          yf = (e-aaf)%5;
          v0 = v0+v-yf;
      }
      else {
          v0 += v;
      }
      e += 1;
      aaf += v;
  }

}
