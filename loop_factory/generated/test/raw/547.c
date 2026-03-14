int main1(int s,int m){
  int il, z00, g, kh, y;

  il=(s%17)+12;
  z00=0;
  g=0;
  kh=0;
  y=5;

  while (1) {
      if (!(g<il&&y>0)) {
          break;
      }
      kh = kh + y;
      g++;
      m += z00;
      y -= 1;
  }

}
