int main1(int b){
  int owm6, rar, xb, odw, xd;

  owm6=b+16;
  rar=-1;
  xb=20;
  odw=1;
  xd=0;

  while (xb>0&&odw<=owm6) {
      if (xb>odw) {
          xb -= odw;
      }
      else {
          xb = 0;
      }
      xd++;
      odw = odw + 1;
      rar++;
  }

}
