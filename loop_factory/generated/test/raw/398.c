int main1(){
  int n9c, xm, q, mh, a;

  n9c=1;
  xm=n9c;
  q=31;
  mh=1;
  a=0;

  while (q>0&&mh<=n9c) {
      if (q>mh) {
          q = q - mh;
      }
      else {
          q = 0;
      }
      mh = mh + 1;
      xm++;
      a++;
  }

}
