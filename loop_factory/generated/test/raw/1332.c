int main1(){
  int n9e, bl7, b, k, mp;

  n9e=1;
  bl7=n9e;
  b=(1%40)+2;
  k=0;
  mp=bl7;

  while (1) {
      if (!(b!=k)) {
          break;
      }
      k = b;
      b = (b+n9e/b)/2;
      mp = mp + k;
  }

}
