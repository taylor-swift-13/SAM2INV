int main73(int u,int t){
  int uy, yiv;

  uy=(u%20)+5;
  yiv=u;

  while (uy>=1) {
      uy -= 1;
      t = t + 3;
      yiv += 4;
      u += uy;
  }

}
