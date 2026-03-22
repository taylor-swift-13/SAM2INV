int main1(int d){
  int rk, j, kwz;

  rk=0;
  j=(d%28)+10;
  kwz=8;

  while (j>rk) {
      j = j - rk;
      rk += 1;
      kwz = kwz + rk;
  }

}
