int main1(int s){
  int e1, kap, m, l2, g, qe9;

  e1=s+16;
  kap=0;
  m=0;
  l2=0;
  g=0;
  qe9=5;

  while (kap<e1) {
      l2 = kap%5;
      if (kap>=qe9) {
          g = (kap-qe9)%5;
          m = m+l2-g;
      }
      else {
          m += l2;
      }
      kap++;
      qe9 += l2;
  }

}
