int main1(int y){
  int y4u2, a9, eig;

  y4u2=y;
  a9=1;
  eig=-3;

  while (a9<=y4u2/2) {
      eig = eig + 1;
      eig = eig+eig*eig;
      y += y4u2;
  }

}
