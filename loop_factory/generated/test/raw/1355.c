int main1(){
  int qmw, zs, va6, pw, h1;

  qmw=1;
  zs=(1%28)+8;
  va6=(1%22)+5;
  pw=0;
  h1=0;

  while (1) {
      if (!(va6!=0)) {
          break;
      }
      if (va6%2==1) {
          pw = pw + zs;
          va6 = va6 - 1;
      }
      va6 = va6/2;
      zs = 2*zs;
      h1 = h1 + va6;
      h1 = h1 + qmw;
  }

}
