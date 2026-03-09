int main1(){
  int wx28, q, l;

  wx28=0;
  q=(1%20)+10;
  l=(1%15)+8;

  while (q>0&&l>0) {
      if (wx28%2==0) {
          q = q - 1;
      }
      else {
          l--;
      }
      wx28 = wx28 + 1;
  }

}
