int main1(int b){
  int b5, m2k, c74, i5u9, ige;

  b5=b+13;
  m2k=0;
  c74=b;
  i5u9=0;
  ige=b;

  while (m2k < b5) {
      m2k += 1;
      i5u9 = i5u9 + (m2k >= (b5 / 2));
      c74 = c74 + 1 + (m2k % 2);
      b = b+(i5u9%6);
      ige = ige+c74+i5u9;
  }

}
