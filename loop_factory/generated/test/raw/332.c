int main1(int y){
  int lqf, v, cj, g9, ga, hw;

  lqf=128;
  v=lqf;
  cj=0;
  g9=-1;
  ga=0;
  hw=0;

  while (g9<=lqf-1) {
      g9++;
      cj = cj + y;
      ga = ga*4;
      hw += g9;
  }

  while (v<hw) {
      cj = cj+hw-g9;
      v++;
      lqf = lqf + y;
      ga = ga+(lqf%3);
  }

}
