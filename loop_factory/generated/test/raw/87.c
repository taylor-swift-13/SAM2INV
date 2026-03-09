int main1(){
  int js, vft, i, vh;

  js=1+3;
  vft=-5;
  i=0;
  vh=0;

  while (vh<js) {
      i = (i+1)%8;
      vh = vh + 1;
      i += vft;
  }

}
