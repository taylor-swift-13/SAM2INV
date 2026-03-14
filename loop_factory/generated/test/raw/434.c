int main1(int e){
  int a, a7, pq, u;

  a=(e%19)+6;
  a7=a;
  pq=0;
  u=e;

  while (pq<a) {
      u = (a)+(-(pq));
      pq += 4;
      e = e + pq;
  }

  while (1) {
      if (!(a7<=a-1)) {
          break;
      }
      a7 += 1;
  }

}
