int main1(int r){
  int hn, xbkk, xm, bq;

  hn=(r%8)+20;
  xbkk=hn;
  xm=hn;
  bq=0;

  while (xbkk>2) {
      xbkk = xbkk - 3;
  }

  while (xbkk>hn) {
      xbkk -= hn;
      xm = xm + bq;
      hn++;
      r = r/3;
      xm = xm*3;
  }

}
