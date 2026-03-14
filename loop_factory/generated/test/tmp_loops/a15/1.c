int main1(int r){
  int io, svq, av, k, ls, b3;

  io=r-9;
  svq=5;
  av=0;
  k=-2;
  ls=-6;
  b3=-1;

  while (k<io) {
      av += r;
      k += 1;
      ls = ls + av;
  }

  while (b3<=io-1) {
      b3 += 1;
      svq += r;
      k = k + b3;
  }

}
