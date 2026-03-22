int main1(){
  int z, y, mjr, yu, e280, tp;

  z=1+7;
  y=z+2;
  mjr=(1%20)+1;
  yu=(1%25)+1;
  e280=0;
  tp=z;

  while (yu!=0) {
      if (yu%2==1) {
          e280 = e280 + mjr;
          yu -= 1;
      }
      else {
      }
      tp = tp + y;
      yu = yu/2;
      mjr = 2*mjr;
      if (tp+1<z) {
          tp = tp%7;
      }
  }

}
