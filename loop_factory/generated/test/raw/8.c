int main1(int m,int a,int t){
  int o, xh, mgf;

  o=0;
  xh=(a%20)+10;
  mgf=(a%15)+8;

  while (1) {
      if (!(xh>0&&mgf>0)) {
          break;
      }
      if (o%2==0) {
          xh = xh - 1;
      }
      else {
          mgf = mgf - 1;
      }
      o = o + 1;
      m = m + o;
  }

}
