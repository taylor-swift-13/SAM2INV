int main1(int w){
  int g1g, d, b, uj;

  g1g=35;
  d=g1g;
  b=7;
  uj=0;

  while (d<g1g) {
      if (d%2==0) {
          if (b>0) {
              b = b - 1;
              uj++;
          }
      }
      else {
          if (uj>0) {
              uj -= 1;
              b += 1;
          }
      }
      d++;
      w = w + g1g;
      w = w - w;
  }

}
