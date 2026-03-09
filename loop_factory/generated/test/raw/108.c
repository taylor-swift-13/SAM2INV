int main1(int q,int w){
  int g, go, mr;

  g=0;
  go=(w%20)+10;
  mr=(w%15)+8;

  for (; go>0&&mr>0; g++) {
      if (!(!(g%2==0))) {
          go -= 1;
      }
      else {
          mr -= 1;
      }
  }

}
