int main1(int l,int s){
  int ys, wq0, pq, ii, ff;

  ys=75;
  wq0=0;
  pq=1;
  ii=0;
  ff=wq0;

  while (1) {
      if (!(pq<=ys)) {
          break;
      }
      ii = ii+2*pq-1;
      l += ys;
      pq = pq + 1;
  }

  while (ii+3<=ff) {
      ii = ii + 3;
  }

}
