int main1(int e){
  int px, q, w1, dd, la, m, kx;

  px=(e%15)+15;
  q=-2;
  w1=5;
  dd=5;
  la=0;
  m=6;
  kx=0;

  while (q<px) {
      if (!(!(q%3==0))) {
          if (w1>0) {
              w1--;
              la++;
          }
      }
      else {
          if (w1<m) {
              w1 = w1 + 1;
              dd += 1;
          }
      }
      q += 1;
      kx += 1;
  }

}
