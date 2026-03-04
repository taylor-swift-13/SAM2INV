int main1(int v,int e){
  int mj, dsh;

  mj=2;
  dsh=(e%15)+3;

  while (dsh!=0) {
      dsh -= 1;
      v = v + mj;
  }

}
