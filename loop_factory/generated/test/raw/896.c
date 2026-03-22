int main1(){
  int i, az, q;

  i=38;
  az=0;
  q=i;

  while (1) {
      if (!(az<i&&q>0)) {
          break;
      }
      q = q - 1;
      az = az + 1;
      az = az+q+q;
      az = az + 1;
  }

}
