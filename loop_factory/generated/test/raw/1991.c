int main1(int t){
  int q, atz, tk, l9;

  q=t*5;
  atz=0;
  tk=13;
  l9=1;

  while (atz < q) {
      tk = tk + 3;
      atz += 1;
      l9 = l9 + 3;
      t = t+l9-tk;
  }

}
