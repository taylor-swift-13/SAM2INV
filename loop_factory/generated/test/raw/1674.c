int main1(){
  int a, oe, but, ms;

  a=1+25;
  oe=0;
  but=-6;
  ms=oe;

  while (oe < a) {
      oe += 1;
      ms = ms+(oe%2);
      but += 4;
  }

}
