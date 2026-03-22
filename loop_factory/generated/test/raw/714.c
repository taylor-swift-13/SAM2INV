int main1(){
  int h, d8, bu, m, ri;

  h=1+24;
  d8=h;
  bu=4;
  m=5;
  ri=(1%35)+8;

  while (ri>0) {
      m = m+ri*ri;
      d8 = d8+bu*bu;
      bu = bu+ri*ri;
      ri--;
      d8 = (5)+(d8*4);
  }

}
