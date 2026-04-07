int main1(int t){
  int kra, l, z, lu;

  kra=t+18;
  l=0;
  z=0;
  lu=kra;

  while (1) {
      if (!(z<kra)) {
          break;
      }
      z += 1;
      l = (l+1)%5;
      lu += l;
  }

}
