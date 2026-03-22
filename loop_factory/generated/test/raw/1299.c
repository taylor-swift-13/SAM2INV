int main1(int h){
  int u, knnc, h6tf, hw;

  u=0;
  knnc=0;
  h6tf=0;
  hw=(h%18)+5;

  while (hw>0) {
      knnc = knnc+h*h;
      hw = (hw)+(-(1));
      h6tf = h6tf+h*h;
      u = u+h*h;
      h = h*4+(h6tf%3)+3;
  }

}
