int main1(){
  int n1, la2, lh, bzg;

  n1=1-9;
  la2=1;
  lh=0;
  bzg=n1;

  while (1) {
      if (!(la2<=n1)) {
          break;
      }
      la2 = 2*la2;
      bzg = (n1)+(bzg);
      lh += 1;
  }

}
