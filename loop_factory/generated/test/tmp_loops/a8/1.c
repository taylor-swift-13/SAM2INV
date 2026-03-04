int main1(int m){
  int s;

  s=(m%15)+3;

  while (s!=0) {
      s -= 1;
      m = m + s;
  }

}
