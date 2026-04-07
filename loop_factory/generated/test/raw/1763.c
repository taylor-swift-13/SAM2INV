int main1(int b){
  int e, jbeo, eve, bct;

  e=b;
  jbeo=0;
  eve=b+1;
  bct=0;

  while (jbeo+1<=e) {
      bct++;
      eve = eve+bct*bct*bct;
      e = (jbeo+1)-1;
  }

}
