int main1(int y){
  int o, uzb, sm, ia;

  o=y-2;
  uzb=0;
  sm=0;
  ia=8;

  while (uzb<o&&ia>0) {
      uzb++;
      sm += ia;
      y += sm;
      ia -= 1;
  }

}
