int main1(){
  int gb, ylt5, k1, i, wnn1, b;

  gb=(1%35)+11;
  ylt5=0;
  k1=0;
  i=0;
  wnn1=0;
  b=0;

  while (ylt5<gb) {
      if (!(!(ylt5%10==0))) {
          if (ylt5%8==0) {
              wnn1++;
          }
          else {
              if (ylt5%6==0) {
                  i = i + 1;
              }
              else {
                  k1 = k1 + 1;
              }
          }
      }
      else {
          b += 1;
      }
      k1 = k1 + 1;
      ylt5 += 1;
  }

}
