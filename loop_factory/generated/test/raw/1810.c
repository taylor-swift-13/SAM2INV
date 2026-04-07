int main1(){
  int f, g0d, u5;

  f=(1%20)+1;
  g0d=(1%25)+1;
  u5=0;

  while (g0d!=0) {
      if (g0d%2==1) {
          u5 += f;
          g0d = g0d - 1;
      }
      else {
      }
      f = 2*f;
      g0d = g0d/2;
  }

}
