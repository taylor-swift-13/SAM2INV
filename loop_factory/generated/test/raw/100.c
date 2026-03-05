int main1(int y,int c){
  int oja, a3, b9;

  oja=(y%8)+11;
  a3=0;
  b9=0;

  while (a3<oja) {
      b9 = oja-b9;
      b9 += 1;
      y += a3;
  }

}
