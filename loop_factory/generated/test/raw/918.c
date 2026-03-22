int main1(int j,int o){
  int dsz, it, fqn, emw;

  dsz=(j%36)+15;
  it=1;
  fqn=0;
  emw=1;

  while (it<=dsz) {
      it = 2*it;
      emw += 1;
      fqn++;
      j = j + it;
  }

}
