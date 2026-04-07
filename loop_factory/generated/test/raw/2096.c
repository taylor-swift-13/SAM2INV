int main1(int k){
  int o2, ks, gb, np;

  o2=k;
  ks=0;
  gb=o2;
  np=0;

  while (1) {
      if (!(ks<=o2-1)) {
          break;
      }
      np = np + ks*k;
      ks = ks + 1;
      gb = (np)+(gb);
  }

}
