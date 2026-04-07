int main1(int b){
  int z7x, ordi, uou, j;

  z7x=b*2;
  ordi=0;
  uou=0;
  j=0;

  while (ordi < z7x) {
      uou = (ordi++, uou + (2*ordi - 1));
      b = b+uou+uou;
      j = j + uou;
      ordi = z7x;
  }

}
