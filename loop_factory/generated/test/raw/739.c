int main1(){
  int y4, us, fu;

  y4=0;
  us=(1%28)+10;
  fu=4;

  while (us>y4) {
      us = us - y4;
      y4 += 1;
      fu = fu+(y4%2);
  }

}
