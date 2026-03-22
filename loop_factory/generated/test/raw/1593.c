int main1(int z){
  int m8b, lg, w, vh, h3, st, xu;

  m8b=z+25;
  lg=0;
  w=22;
  vh=0;
  h3=1;
  st=0;
  xu=-6;

  while (w>0&&lg<m8b) {
      if (w<h3) {
          st = w;
      }
      else {
          st = h3;
      }
      vh = vh + st;
      w = w - st;
      if (lg%2==0) {
          h3 += 2;
      }
      else {
          h3 += 1;
      }
      lg++;
      z = z + w;
      xu = xu + 3;
      xu = xu + 1;
  }

}
