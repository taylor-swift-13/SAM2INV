int main1(int u,int w){
  int tyk, g9b, b;

  tyk=u;
  g9b=-2;
  b=u;

  while (1) {
      if (!(g9b<=tyk-1)) {
          break;
      }
      u--;
      b += 1;
      w += b;
      g9b = g9b + 1;
  }

}
