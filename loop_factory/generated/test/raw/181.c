int main1(int d,int g){
  int xshy, b, vl;

  xshy=d+11;
  b=xshy;
  vl=0;

  for (; b-1>=0; b = b - 1) {
      d = d + g;
      g += vl;
      d = d + g;
  }

}
