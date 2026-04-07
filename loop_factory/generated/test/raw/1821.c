int main1(int a){
  int nfj, zy0, w0, kf, d7f8;

  nfj=9;
  zy0=0;
  w0=nfj;
  kf=0;
  d7f8=(a%35)+8;

  while (1) {
      if (!(d7f8>=1)) {
          break;
      }
      zy0 = zy0+w0*w0;
      kf = kf+d7f8*d7f8;
      w0 = w0+d7f8*d7f8;
      d7f8 -= 1;
      a = a+d7f8+zy0;
  }

}
