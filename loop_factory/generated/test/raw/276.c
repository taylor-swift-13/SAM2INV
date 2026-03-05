int main1(){
  int iq, ko, u3, gy;

  iq=(1%25)+8;
  ko=2;
  u3=1;
  gy=iq;

  while (ko<=iq-2) {
      if (u3==1) {
          u3 = 2;
      }
      else {
          if (u3==2) {
              u3 = 1;
          }
      }
      gy += u3;
      gy += ko;
  }

}
