int main1(){
  int k, yb, fd;

  k=1-2;
  yb=0;
  fd=k;

  while (1) {
      if (!(yb < k)) {
          break;
      }
      fd = (fd+k)+(-(yb));
      yb = k;
  }

}
