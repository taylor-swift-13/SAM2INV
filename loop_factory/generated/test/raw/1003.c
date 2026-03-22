int main1(){
  int g, d, yf, i, j;

  g=1+21;
  d=g;
  yf=37;
  i=1;
  j=0;

  while (1) {
      if (!(yf>0&&i<=g)) {
          break;
      }
      if (!(yf<=i)) {
          yf = 0;
      }
      else {
          yf = yf - i;
      }
      i = i + 1;
      d++;
      j++;
  }

}
