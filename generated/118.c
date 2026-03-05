int main118(int f,int d){
  int hw, yg, ad;

  hw=f*2;
  yg=0;
  ad=d;

  while (yg<=hw-1) {
      yg += 6;
      if (yg%5==0) {
          yg += 1;
      }
      ad = ad + hw;
      ad += 1;
      f = f + ad;
  }

}
