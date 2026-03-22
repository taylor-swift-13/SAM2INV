int main1(int t,int m){
  int x8, lr, p6, wril, k6gi, rrh;

  x8=(t%15)+10;
  lr=x8;
  p6=lr;
  wril=lr;
  k6gi=-4;
  rrh=8;

  while (rrh<=x8) {
      p6 += wril;
      wril = wril + k6gi;
      t += lr;
      k6gi += 2;
      rrh += 1;
      t = t*2;
  }

}
