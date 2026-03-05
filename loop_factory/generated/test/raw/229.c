int main1(int n){
  int qfv, m;

  qfv=(n%25)+13;
  m=1;

  while (m<=qfv) {
      m = m + m;
      m++;
      n = n + m;
  }

}
