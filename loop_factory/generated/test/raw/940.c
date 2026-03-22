int main1(){
  int fc, ta, n;

  fc=0;
  ta=(1%20)+10;
  n=(1%15)+8;

  while (ta>0&&n>0) {
      if (!(!(fc%2==0))) {
          ta--;
      }
      else {
          n = n - 1;
      }
      fc = fc + 1;
  }

}
