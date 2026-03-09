int main1(int e){
  int to, oi, bj, ks;

  to=e;
  oi=5;
  bj=0;
  ks=e;

  while (oi<=to) {
      bj = bj+2*oi-1;
      oi = oi + 1;
      ks += 2;
      e += oi;
  }

}
