int main1(int j){
  int uc1, uu, afe;

  uc1=14;
  uu=0;
  afe=0;

  while (1) {
      if (!(uu<=18)) {
          break;
      }
      if (!(uc1>=0)) {
          uc1 = uc1+-4;
          afe = afe + 1;
      }
      else {
          uc1 = uc1 + 32;
      }
      uu = uu + 1;
  }

}
