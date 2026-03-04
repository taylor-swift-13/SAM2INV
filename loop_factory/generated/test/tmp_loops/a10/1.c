int main1(int p){
  int z;

  z=(p%15)+3;

  while (z!=0) {
      z = z - 1;
      p += z;
  }

}
