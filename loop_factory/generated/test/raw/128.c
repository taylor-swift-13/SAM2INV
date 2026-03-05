int main1(int g,int w){
  int ls, f3, g21y;

  ls=w;
  f3=ls;
  g21y=4;

  while (f3<ls) {
      g21y = f3%5;
      if (f3>=g21y) {
          g21y = (f3-g21y)%5;
          g21y = g21y+g21y-g21y;
      }
      else {
          g21y = g21y + g21y;
      }
      f3 = f3 + 1;
      g = g + g21y;
  }

}
