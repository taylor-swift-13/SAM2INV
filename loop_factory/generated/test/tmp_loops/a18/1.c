int main1(int g){
  int w, ff;

  w=0;
  ff=(g%15)+3;

  while (ff!=0) {
      ff--;
      g = g + w;
  }

}
