int main1(int t){
  int e, u, hj;

  e=t+14;
  u=e;
  hj=4;

  while (u<e) {
      hj = u%5;
      if (u>=hj) {
          hj = (u-hj)%5;
          hj = hj+hj-hj;
      }
      else {
          hj += hj;
      }
      u = u + 1;
      t += hj;
  }

}
