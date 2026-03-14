int main1(int x){
  int ar9, ye, d5rm, f, o2;

  ar9=56;
  ye=0;
  d5rm=0;
  f=x;
  o2=ar9;

  while (d5rm<ar9) {
      ye = (ye+1)%8;
      d5rm++;
      f += ye;
      f = f+o2+x;
  }

}
