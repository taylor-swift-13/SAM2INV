int main187(int k,int y,int n){
  int tkg;

  tkg=(k%20)+5;

  while (tkg>0) {
      tkg = tkg - 1;
      k += 1;
      y += tkg;
      y = y + k;
  }

}
