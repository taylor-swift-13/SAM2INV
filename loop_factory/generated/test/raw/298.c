int main1(int f,int a){
  int f6, yj, g9au, fbq;

  f6=f;
  yj=f6;
  g9au=0;
  fbq=a;

  while (g9au<f6) {
      fbq = f6-g9au;
      g9au += 1;
      f += g9au;
  }

  while (1) {
      if (!(yj<g9au)) {
          break;
      }
      yj += 1;
      f += g9au;
      f6 = g9au-yj;
  }

}
