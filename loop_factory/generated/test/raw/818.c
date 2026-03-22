int main1(int i,int h){
  int sg, bc, lx, v3g;

  sg=h;
  bc=1;
  lx=0;
  v3g=1;

  while (1) {
      if (!(bc<=sg-1)) {
          break;
      }
      v3g = v3g+lx*bc;
      bc = sg;
  }

}
