int main1(){
  int k86, j, le, ct3, xq, g3a7;

  k86=(1%40)+16;
  j=0;
  le=j;
  ct3=0;
  xq=0;
  g3a7=k86;

  while (j < k86) {
      ct3 = ct3 + le;
      xq += g3a7;
      j++;
      g3a7 = g3a7+(xq%4);
  }

}
