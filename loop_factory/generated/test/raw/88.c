int main1(){
  int gw, kuar, kl8b, ss;

  gw=74;
  kuar=0;
  kl8b=0;
  ss=10;

  while (1) {
      if (!(kl8b<=gw-1)) {
          break;
      }
      kuar = (kuar+1)%3;
      kl8b = kl8b + 1;
      ss = ss + kuar;
      ss = ss + 3;
  }

}
