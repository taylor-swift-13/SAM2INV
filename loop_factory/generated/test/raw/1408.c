int main1(int w){
  int gd, n4t8, wqg, wt;

  gd=(w%8)+7;
  n4t8=gd;
  wqg=0;
  wt=gd;

  while (wqg<gd&&wt>0) {
      wt -= 1;
      w = w+gd-n4t8;
      wqg = (1)+(wqg);
  }

}
