int main1(int i){
  int rh;

  rh=(i%15)+3;

  while (rh!=0) {
      rh = rh - 1;
      i += rh;
  }

}
