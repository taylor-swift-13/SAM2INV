int main1(int o){
  int n, sjx, wq;

  n=13;
  sjx=0;
  wq=11;

  while (1) {
      if (!(sjx<n)) {
          break;
      }
      sjx += 1;
      wq = n-sjx;
      o += wq;
  }

}
