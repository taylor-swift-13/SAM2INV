int main1(int k){
  int h8, yf, bu;

  h8=2;
  yf=(k%20)+10;
  bu=(k%15)+8;

  while (1) {
      if (!(yf>0&&bu>0)) {
          break;
      }
      if (!(!(h8%2==0))) {
          yf -= 1;
      }
      else {
          bu = bu - 1;
      }
      h8++;
  }

}
