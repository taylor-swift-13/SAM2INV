int main1(){
  int gjt, n, v4, ad, v0h;

  gjt=(1%28)+14;
  n=2;
  v4=0;
  ad=gjt;
  v0h=-6;

  while (1) {
      if (!(n<=gjt)) {
          break;
      }
      v4 = v4+n*n;
      n += 1;
      ad = ad + 3;
      v0h += n;
  }

}
