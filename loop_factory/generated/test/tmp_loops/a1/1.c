int main1(int i){
  int cu;

  cu=(i%15)+3;

  while (cu!=0) {
      cu--;
      i += cu;
  }

}
