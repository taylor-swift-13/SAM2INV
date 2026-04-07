int main1(int j){
  int zh, nep, l9u, ypa;

  zh=(j%21)+15;
  nep=0;
  l9u=j;
  ypa=zh;

  while (nep<zh) {
      ypa = ypa + 1;
      l9u = ypa*ypa;
      j = j+(ypa%9);
      nep = zh;
  }

}
