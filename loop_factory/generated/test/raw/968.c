int main1(){
  int lzm, qf1, ou;

  lzm=(1%20)+5;
  qf1=(1%20)+5;
  ou=(1%20)+5;

  while (lzm>0) {
      if (qf1>0) {
          if (ou>0) {
              lzm--;
              qf1--;
              ou--;
          }
      }
      qf1 = qf1 + 1;
  }

}
