int main1(int x,int p){
  int wed, mq, t4, sml, mkn;

  wed=0;
  mq=(x%20)+1;
  t4=(x%25)+1;
  sml=0;
  mkn=2;

  while (t4!=0) {
      if (t4%2==1) {
          sml += mq;
          t4--;
      }
      else {
      }
      mq = 2*mq;
      x += wed;
      mkn += 2;
      t4 = t4/2;
  }

}
