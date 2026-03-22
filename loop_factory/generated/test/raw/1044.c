int main1(){
  int b, cho, i6, t2, waxr;

  b=(1%30)+6;
  cho=b;
  i6=1;
  t2=0;
  waxr=cho;

  while (i6<=b) {
      t2 = t2+2*i6-1;
      i6 = i6 + 1;
      waxr += b;
  }

  while (1) {
      if (!(waxr<=t2-1)) {
          break;
      }
      cho = t2-waxr;
      waxr = waxr + 5;
      cho = cho + i6;
  }

}
